# made 100% with ai claude sonnet
import bpy
import bmesh
import re
import traceback
from math import degrees
from time import perf_counter

# ---------------- Настройки ----------------
POLL_INTERVAL      = 0.15   # как часто проверять состояние (сек); подстраивается под тяжёлые сцены
MAX_DETAILED_VERTS = 10     # у скольких вершин выводить координаты (остальные — только индексы)
MAX_LIST_ITEMS     = 60
PRECISION          = 4
LOG_TOOL           = True   # писать смену активного инструмента
LOG_SETTINGS       = True   # писать смену pivot / snap / proportional / mirror
PENDING_TICKS      = 3      # сколько тактов ждать оператор, прежде чем писать "? undo/redo"
# --------------------------------------------

IGNORE_PREFIX = ("screen.", "ui.", "outliner.", "text.", "console.", "info.", "file.",
                 "image.", "graph.", "action.", "node.", "sequencer.", "clip.", "wm.",
                 "render.", "scene.", "ed.", "preferences.", "buttons.", "nla.", "mask.")
NOISE = {"rna_type", "orient_matrix", "orient_matrix_type", "orient_axis_ortho",
         "release_confirm", "cursor_transform", "texture_space", "remove_on_cancel",
         "view2d_edge_pan", "alt_navigation", "use_accurate", "gpencil_strokes",
         "use_duplicated_keyframes", "center_override", "mirror", "use_automerge_and_split"}
_SELECT_RE = re.compile(r"(^|_)select($|_)")

_outbox = []
_prev = None
_prev_ptrs = set()
_prev_len = 0
_last_ptr = None
_last_params = None
_pending = 0


# ---------- форматирование ----------
def num(x):
    s = f"{x:.{PRECISION}f}".rstrip("0").rstrip(".")
    return "0" if s in ("-0", "") else s


def vec(v):
    return "(" + ",".join(num(c) for c in v) + ")"


def lst(items):
    items = list(items)
    if len(items) > MAX_LIST_ITEMS:
        return ",".join(map(str, items[:MAX_LIST_ITEMS])) + f",…+{len(items) - MAX_LIST_ITEMS}"
    return ",".join(map(str, items))


def ranges(indices):
    idx = sorted(indices)
    out, i = [], 0
    while i < len(idx):
        j = i
        while j + 1 < len(idx) and idx[j + 1] == idx[j] + 1:
            j += 1
        out.append(str(idx[i]) if i == j else f"{idx[i]}-{idx[j]}")
        i = j + 1
    if len(out) > MAX_LIST_ITEMS:
        return ",".join(out[:MAX_LIST_ITEMS]) + f",…+{len(out) - MAX_LIST_ITEMS}"
    return ",".join(out)


def fmt_val(v):
    if isinstance(v, bool):
        return str(v)
    if isinstance(v, float):
        return num(v)
    if isinstance(v, (int, str)):
        return str(v)
    if isinstance(v, (tuple, list)):
        return "(" + ",".join(fmt_val(x) for x in v) + ")"
    return str(v)


def fmt_params(d):
    parts = []
    for k, v in d.items():
        if isinstance(v, dict):
            parts.append(f"{k}{{{fmt_params(v)}}}")
        else:
            parts.append(f"{k}={fmt_val(v)}")
    return " ".join(parts)


# ---------- параметры оператора ----------
def op_id(op):
    """TRANSFORM_OT_translate -> transform.translate"""
    n = op.bl_idname
    if "_OT_" in n:
        cat, _, fn = n.partition("_OT_")
        return f"{cat.lower()}.{fn}"
    return n


def norm(val):
    if isinstance(val, (str, bool, int, float)):
        return val
    if isinstance(val, (set, frozenset)):
        return tuple(sorted(val))
    try:
        return tuple(norm(x) for x in val)
    except TypeError:
        return str(val)


def is_default(val, prop):
    try:
        t = prop.type
        if t in ('BOOLEAN', 'INT', 'FLOAT'):
            if prop.array_length > 0:
                d, v = tuple(prop.default_array), tuple(val)
                return len(d) == len(v) and all(abs(a - b) < 1e-6 for a, b in zip(d, v))
            return abs(val - prop.default) < 1e-6
        if t == 'ENUM':
            return val == (prop.default_flag if prop.is_enum_flag else prop.default)
        if t == 'STRING':
            return val == prop.default
    except Exception:
        pass
    return False


def collect_props(props, depth, idname):
    out = {}
    if depth > 2:
        return out
    skip_def = depth > 0 or idname.startswith("transform.")
    rna_props = props.bl_rna.properties
    for prop in rna_props:
        name = prop.identifier
        if name in NOISE:
            continue
        try:
            if prop.type == 'POINTER':
                sub_id = name.replace("_OT_", ".").lower()
                sub = collect_props(getattr(props, name), depth + 1, sub_id)
                if sub:
                    out[sub_id] = sub
                continue
            if prop.type == 'COLLECTION' or not props.is_property_set(name):
                continue
            val = getattr(props, name)
            if skip_def and is_default(val, prop):
                continue
            out[name] = norm(val)
        except Exception:
            continue

    ca = out.pop("constraint_axis", None)
    if ca:
        out["axis"] = "".join(a for a, f in zip("XYZ", ca) if f)

    if "use_proportional_edit" in rna_props:
        if out.get("use_proportional_edit"):
            for k in ("proportional_size", "proportional_edit_falloff"):
                try:
                    out[k] = norm(getattr(props, k))
                except Exception:
                    pass
        else:
            for k in [k for k in out if k.startswith(("proportional_", "use_proportional_"))]:
                del out[k]
    if "snap" in rna_props and not out.get("snap"):
        for k in [k for k in out if k.startswith(("snap_", "use_snap_"))]:
            del out[k]

    if idname == "transform.rotate":
        try:
            out.setdefault("orient_axis", props.orient_axis)
        except Exception:
            pass
        v = out.get("value")
        if isinstance(v, (int, float)) and not isinstance(v, bool):
            out["deg"] = round(degrees(v), 2)
    return out


def safe_params(op):
    try:
        return fmt_params(collect_props(op.properties, 0, op_id(op)))
    except Exception:
        return ""


def is_ignored(idname):
    if idname.startswith(IGNORE_PREFIX):
        return True
    cat, _, fn = idname.partition(".")
    if _SELECT_RE.search(fn) or fn.endswith("_pick"):
        return True
    if cat == "view3d" and not fn.startswith(("edit_mesh", "snap_selected")):
        return True
    return False


# ---------- вывод в Info ----------
def emit(tag, msg):
    _outbox.append(f"[{tag}] {msg}")


class WM_OT_act_logger_flush(bpy.types.Operator):
    """Выводит накопленные строки лога в Info"""
    bl_idname = "wm.act_logger_flush"
    bl_label = "Action Logger Flush"
    bl_options = {'INTERNAL'}

    def execute(self, context):
        lines = list(_outbox)
        _outbox.clear()
        for line in lines:
            self.report({'INFO'}, line)
        return {'FINISHED'}


def flush():
    if not _outbox:
        return
    try:
        bpy.ops.wm.act_logger_flush()
    except Exception:
        for line in _outbox:
            print(line)
        _outbox.clear()


# ---------- состояние ----------
def mode_name(ao):
    if ao is None:
        return "OBJECT"
    if ao.mode == 'EDIT':
        return "EDIT_" + ao.type
    return ao.mode


def get_tool(mode):
    try:
        ws = getattr(bpy.context, "workspace", None)
        if ws is None:
            wins = bpy.context.window_manager.windows
            ws = wins[0].workspace if wins else None
        if ws is None:
            return None
        t = ws.tools.from_space_view3d_mode(mode, create=False)
        return t.idname if t else None
    except Exception:
        return None


def settings_str(scene, ao, mode):
    ts = scene.tool_settings
    edit = mode.startswith("EDIT")
    try:
        orient = scene.transform_orientation_slots[0].type
    except Exception:
        orient = "?"
    parts = [f"pivot={ts.transform_pivot_point}", f"orient={orient}"]
    if ts.use_snap:
        try:
            parts.append("snap=" + ",".join(sorted(ts.snap_elements)))
        except Exception:
            parts.append("snap=on")
    else:
        parts.append("snap=off")
    prop_on = ts.use_proportional_edit if edit else ts.use_proportional_edit_objects
    parts.append(f"prop={ts.proportional_edit_falloff}" if prop_on else "prop=off")
    if mode == "EDIT_MESH":
        if ts.use_mesh_automerge:
            parts.append("automerge")
        me = ao.data
        ax = "".join(a for a, f in zip("XYZ", (me.use_mirror_x, me.use_mirror_y, me.use_mirror_z)) if f)
        parts.append(f"mirror={ax or 'off'}")
    return " ".join(parts)


def take_state():
    ctx = bpy.context
    vl = ctx.view_layer
    scene = ctx.scene
    ao = vl.objects.active
    mode = mode_name(ao)
    ts = scene.tool_settings
    st = {
        "mode": mode,
        "sel_mode": "".join(n for n, f in zip("VEF", ts.mesh_select_mode) if f),
        "meshes": {},
        "objs": None,
        "nobj": len(vl.objects),
        "tool": get_tool(mode) if LOG_TOOL else None,
        "settings": None,
    }
    try:
        if LOG_SETTINGS:
            st["settings"] = settings_str(scene, ao, mode)
    except Exception:
        pass

    if mode == "EDIT_MESH":
        for obj in vl.objects:
            if obj.type != 'MESH' or obj.mode != 'EDIT':
                continue
            bm = bmesh.from_edit_mesh(obj.data)
            bm.verts.index_update()
            bm.edges.index_update()
            bm.faces.index_update()
            act = bm.select_history.active
            st["meshes"][obj.name] = {
                "v": tuple(v.index for v in bm.verts if v.select),
                "e": tuple(e.index for e in bm.edges if e.select),
                "f": tuple(f.index for f in bm.faces if f.select),
                "act": (type(act).__name__[2].lower() + str(act.index)) if act is not None else None,
                "n": (len(bm.verts), len(bm.edges), len(bm.faces)),
            }
    else:
        st["objs"] = (tuple(sorted(o.name for o in vl.objects if o.select_get())),
                      ao.name if ao else None)
    return st


def sel_sig(st):
    return (st["mode"], st["objs"],
            st["sel_mode"] if st["meshes"] else None,
            tuple((n, m["v"], m["e"], m["f"], m["act"], m["n"])
                  for n, m in sorted(st["meshes"].items())))


# ---------- описание выделения: одна строка на вершину ----------
def emit_selection(st):
    if not st["meshes"]:
        names, act = st["objs"] or ((), None)
        emit("SEL", f"mode={st['mode']} objects: {lst(names) or 'none'}"
                    + (f" active={act}" if act else ""))
        return

    for name, m in st["meshes"].items():
        obj = bpy.data.objects.get(name)
        if obj is None:
            continue
        sv = m["v"]
        if not sv:
            emit("SEL", f"{name}: ничего не выделено")
            continue

        bm = bmesh.from_edit_mesh(obj.data)
        bm.verts.index_update()
        bm.verts.ensure_lookup_table()

        for vi in sv[:MAX_DETAILED_VERTS]:
            v = bm.verts[vi]
            mark = "*" if m["act"] == f"v{vi}" else ""   # * = активная вершина
            emit("SEL", f"{name} v{vi}{mark} local{vec(v.co)}")

        rest = sv[MAX_DETAILED_VERTS:]
        if rest:
            emit("SEL", f"{name} ещё {len(rest)} вершин (без координат): v{ranges(rest)}")


# ---------- описание действия ----------
def before_str(prev):
    if prev["meshes"]:
        mode = prev["sel_mode"]
        parts = []
        for name, m in prev["meshes"].items():
            s = f"'{name}' v:{ranges(m['v']) or '-'}"
            if mode == "E":
                s += f" e:{ranges(m['e']) or '-'}"
            if mode == "F":
                s += f" f:{ranges(m['f']) or '-'}"
            parts.append(s)
        return f"on[{mode}] " + "; ".join(parts)
    if prev["objs"]:
        names, act = prev["objs"]
        return f"on objects {lst(names) or 'none'}" + (f" active={act}" if act else "")
    return ""


def delta_str(prev, cur):
    parts = []
    for name, m in cur["meshes"].items():
        p = prev["meshes"].get(name)
        if p and p["n"] != m["n"]:
            a, b = p["n"], m["n"]
            parts.append(f"topology '{name}': v{a[0]}→{b[0]} e{a[1]}→{b[1]} f{a[2]}→{b[2]}")
    if prev["nobj"] != cur["nobj"]:
        parts.append(f"objects {prev['nobj']}→{cur['nobj']}")
    return " | ".join(parts)


def emit_action(op, params, prev, cur):
    parts = [op_id(op) + (" " + params if params else "")]
    for extra in (before_str(prev), delta_str(prev, cur)):
        if extra:
            parts.append(extra)
    emit("ACT", " | ".join(parts))


# ---------- определение новых операторов ----------
def detect_new_op():
    """Возвращает (op, params), если с прошлой проверки появился новый оператор."""
    global _prev_ptrs, _prev_len, _last_ptr, _last_params
    ops = bpy.context.window_manager.operators
    n = len(ops)
    if n == 0:
        _prev_ptrs, _prev_len, _last_ptr, _last_params = set(), 0, None, None
        return None, None
    op = ops[n - 1]
    ptr = op.as_pointer()
    params = safe_params(op)
    new = (ptr not in _prev_ptrs) or (n > _prev_len) or (ptr == _last_ptr and params != _last_params)
    _prev_ptrs = {o.as_pointer() for o in ops}
    _prev_len, _last_ptr, _last_params = n, ptr, params
    return (op, params) if new else (None, None)


def modal_running():
    """True, пока выполняется модальный оператор (перемещение, поворот, экструд мышью...)"""
    try:
        for w in bpy.context.window_manager.windows:
            for mop in w.modal_operators:
                if not is_ignored(op_id(mop)):
                    return True
    except Exception:
        pass
    return False


def process():
    global _prev, _pending
    if modal_running():
        return  # ждём завершения операции, состояние «до» не трогаем

    cur = take_state()
    op, params = detect_new_op()

    if _prev is None:
        _prev = cur
        emit("ACT", f"logger on | mode={cur['mode']}")
        if cur["settings"]:
            emit("SET", cur["settings"])
        if cur["tool"]:
            emit("TOOL", cur["tool"])
        emit_selection(cur)
        return

    prev = _prev
    mode_changed = cur["mode"] != prev["mode"]
    sel_changed = sel_sig(cur) != sel_sig(prev)

    # состояние изменилось, а оператора ещё нет: возможно, он вот-вот появится
    if op is None and sel_changed and not mode_changed:
        _pending += 1
        if _pending < PENDING_TICKS:
            return
    _pending = 0
    _prev = cur

    if cur["settings"] and cur["settings"] != prev["settings"] and not mode_changed:
        emit("SET", cur["settings"])
    if cur["tool"] and cur["tool"] != prev["tool"] and not mode_changed:
        emit("TOOL", cur["tool"])

    if op is not None and not is_ignored(op_id(op)):
        emit_action(op, params, prev, cur)
    elif op is None and sel_changed:
        if mode_changed:
            emit("MODE", f"{prev['mode']}→{cur['mode']}")
        else:
            d = delta_str(prev, cur)
            emit("ACT", "? undo/redo или правка без оператора" + (" | " + d if d else ""))

    if sel_changed:
        emit_selection(cur)


# ---------- таймер ----------
def make_tick(token):
    def tick():
        if bpy.app.driver_namespace.get("act_logger_token") is not token:
            return None  # скрипт запущен заново или выключен — старый таймер умирает
        t0 = perf_counter()
        try:
            process()
            flush()
        except Exception:
            traceback.print_exc()
        return max(POLL_INTERVAL, (perf_counter() - t0) * 4)
    return tick


def register():
    # --- убрать остатки прошлых версий скрипта ---
    for h in list(bpy.app.handlers.depsgraph_update_post):
        if getattr(h, "__name__", "") == "_on_depsgraph_update":
            bpy.app.handlers.depsgraph_update_post.remove(h)
    for cls_name in ("MESH_OT_report_selected_verts_info", "WM_OT_act_logger_flush"):
        old = getattr(bpy.types, cls_name, None)
        if old is not None:
            try:
                bpy.utils.unregister_class(old)
            except Exception:
                pass

    bpy.utils.register_class(WM_OT_act_logger_flush)
    token = object()
    bpy.app.driver_namespace["act_logger_token"] = token
    bpy.app.timers.register(make_tick(token), first_interval=0.3, persistent=True)
    print("[ACT] Логирование действий включено")


def unregister():
    bpy.app.driver_namespace["act_logger_token"] = None
    try:
        bpy.utils.unregister_class(WM_OT_act_logger_flush)
    except Exception:
        pass
    print("[ACT] Логирование выключено")


register()
