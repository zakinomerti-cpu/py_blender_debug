#made 100% by claude sonnet
import bpy
import bmesh
import re
import traceback
from array import array
from math import degrees
from time import perf_counter
from bpy.app.handlers import persistent

# ---------------- Настройки ----------------
POLL_INTERVAL      = 0.05      # как часто проверять состояние (сек); сам замедляется на тяжёлых мешах
MAX_LIST_ITEMS     = 100000    # максимум элементов в списках индексов
ITEMS_PER_LINE     = 0         # 0 = весь список одной строкой; иначе разбивать по N пар на строку
PRECISION          = 4         # знаков после запятой
LOG_TOOL           = True      # писать смену активного инструмента
LOG_SETTINGS       = True      # писать смену pivot / snap / proportional / mirror
PENDING_TICKS      = 8         # тактов ожидания оператора в Edit Mode, если менялась топология
MAX_STEPS          = 500       # длина истории шагов в логе
# --- Sculpt ---
MAX_SCULPT_VERTS   = 100000    # мешей больше этого размера скрипт в Sculpt Mode не сравнивает
MOVE_EPS           = 1e-6      # смещение меньше этого значения считается нулевым
SCULPT_QUIET_TICKS = 2         # мазок записывается, когда вершины не менялись столько тактов подряд
DEBUG              = False     # True = печатать диагностику скульптинга в системную консоль
# --------------------------------------------

IGNORE_PREFIX = ("screen.", "ui.", "outliner.", "text.", "console.", "info.", "file.",
                 "image.", "graph.", "action.", "node.", "sequencer.", "clip.", "wm.",
                 "render.", "scene.", "ed.", "preferences.", "buttons.", "nla.", "mask.")
NOISE = {"rna_type", "orient_matrix", "orient_matrix_type", "orient_axis_ortho",
         "release_confirm", "cursor_transform", "texture_space", "remove_on_cancel",
         "view2d_edge_pan", "alt_navigation", "use_accurate", "gpencil_strokes",
         "use_duplicated_keyframes", "center_override", "mirror", "use_automerge_and_split"}
MODE_OPS = ("sculpt.sculptmode_toggle", "object.mode_set", "object.editmode_toggle")
STROKE_LABEL = "sculpt.stroke(inferred)"
_SELECT_RE = re.compile(r"(^|_)select($|_)")

_outbox = []
_events = []          # 'undo' / 'redo' от обработчиков Blender
_steps = []           # история шагов: ("act", имя_оператора) или ("sel", краткое_описание)
_pos = 0              # сколько шагов сейчас применено (Undo уменьшает, Redo увеличивает)
_prev = None
_prev_ptrs = set()
_prev_len = 0
_last_ptr = None
_last_params = None
_pending = 0
_sel_n = 0
_mode_op_wait = 0     # тактов, пока ждём оператор смены режима, уже записанной как "mode A→B"
_sculpt_snap = {}     # {имя объекта: array('f') длиной n*3} координаты после прошлой записи
_sculpt_last = {}     # показания на прошлом такте (для определения конца мазка)
_sculpt_quiet = 0     # сколько тактов подряд вершины не менялись
_sculpt_warned = set()
_dbg_modal = None


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


def chunked(tag, head, items):
    """items — готовые строки вида '(i,(x,y,z))'. Выводит 'head: [...]'."""
    step = ITEMS_PER_LINE or len(items) or 1
    for s in range(0, len(items), step):
        emit(tag, f"{head}: [" + ",".join(items[s:s + step]) + "]")


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


# ---------- история шагов: счётчик действий, Undo / Redo ----------
def acts_applied():
    """Сколько действий сейчас применено (выбор вершин не считается)."""
    return sum(1 for k, _ in _steps[:_pos] if k == "act")


def push_step(kind, label):
    """Новый шаг; ветка Redo после него теряется (как в Blender). Возвращает число действий."""
    global _pos
    del _steps[_pos:]
    _steps.append((kind, label))
    if len(_steps) > MAX_STEPS:
        del _steps[0]
    _pos = len(_steps)
    return acts_applied()


def emit_history(kind):
    global _pos
    if kind == "undo":
        if _pos == 0:
            emit("UNDO", f"Ctrl+Z: в логе нет шага для отмены | действий: {acts_applied()}")
            return
        _pos -= 1
        k, label = _steps[_pos]
        if k == "act":
            emit("UNDO", f"Ctrl+Z: отмена действия #{acts_applied() + 1} {label} "
                         f"→ действий: {acts_applied()}")
        else:
            emit("UNDO", f"Ctrl+Z: отмена выбора ({label}), это не действие "
                         f"→ действий: {acts_applied()}")
    else:
        if _pos >= len(_steps):
            emit("REDO", f"Ctrl+Shift+Z: в логе нет шага для повтора | действий: {acts_applied()}")
            return
        k, label = _steps[_pos]
        _pos += 1
        if k == "act":
            emit("REDO", f"Ctrl+Shift+Z: повтор действия #{acts_applied()} {label} "
                         f"→ действий: {acts_applied()}")
        else:
            emit("REDO", f"Ctrl+Shift+Z: повтор выбора ({label}), это не действие "
                         f"→ действий: {acts_applied()}")


@persistent
def _on_undo_post(*args):
    _events.append("undo")


@persistent
def _on_redo_post(*args):
    _events.append("redo")


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
    if mode == "EDIT_MESH" and ts.use_mesh_automerge:
        parts.append("automerge")
    if mode in ("EDIT_MESH", "SCULPT"):
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


def sel_brief(st):
    if st["meshes"]:
        return "; ".join(f"{n} v:{ranges(m['v']) or '-'}" for n, m in st["meshes"].items())
    names, _act = st["objs"] or ((), None)
    return "objects: " + (lst(names) or "none")


def topo_changed(prev, cur):
    """True, если у какого-то меша изменилось число вершин, рёбер или граней."""
    for n, m in cur["meshes"].items():
        p = prev["meshes"].get(n)
        if p is None or p["n"] != m["n"]:
            return True
    return False


# ---------- описание выделения: меш: [(индекс, локальная позиция), ...] ----------
def emit_selection(st):
    global _sel_n
    _sel_n += 1
    emit("SEL", f"────── выбор #{_sel_n} ──────")
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

        items = [f"({vi},{vec(bm.verts[vi].co)})" for vi in sv]
        head = f"{name} sel({len(sv)}) local"
        if m["act"]:
            head += f" active={m['act']}"
        chunked("SEL", head, items)


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


def loopcut_info(cur):
    """Плоскость разреза по новым (выделенным) вершинам: на какой оси координата постоянна."""
    out = []
    for name, m in cur["meshes"].items():
        obj = bpy.data.objects.get(name)
        if obj is None or not m["v"]:
            continue
        bm = bmesh.from_edit_mesh(obj.data)
        bm.verts.ensure_lookup_table()
        co = [bm.verts[i].co for i in m["v"] if i < len(bm.verts)]
        planes = []
        for k, a in enumerate("xyz"):
            vals = [c[k] for c in co]
            if vals and max(vals) - min(vals) < 1e-4:
                planes.append(f"{a}={num(vals[0])}")
        if planes:
            out.append(f"cut plane (local) {','.join(planes)} new loop v{ranges(m['v'])}")
    return " | ".join(out)


def emit_action(n, op, params, prev, cur):
    oid = op_id(op)
    parts = [oid + (" " + params if params else "")]
    if oid.startswith("mesh.loopcut"):
        extras = (delta_str(prev, cur), loopcut_info(cur))   # loop cut не использует выделение
    else:
        extras = (before_str(prev), delta_str(prev, cur))
    for extra in extras:
        if extra:
            parts.append(extra)
    emit(f"ACT #{n}", " | ".join(parts))


def verts_change(prev, cur, by_history):
    """Пишет строку только если число вершин в меше (Edit Mode) изменилось."""
    for name, m in cur["meshes"].items():
        p = prev["meshes"].get(name)
        if not p:
            continue
        a, b = p["n"][0], m["n"][0]
        if a == b:
            continue
        tail = " (undo/redo)" if by_history else ""
        if b > a:
            emit("VERTS", f"{name} +{b - a} вершин ({a}→{b}) новые: v{ranges(range(a, b))}{tail}")
        else:
            emit("VERTS", f"{name} −{a - b} вершин ({a}→{b}){tail}")


# ---------- Sculpt Mode: смещения вершин после каждого мазка ----------
def brush_str():
    """Настройки кисти. Каждое поле читается отдельно: одна ошибка не отбрасывает остальные."""
    try:
        ts = bpy.context.scene.tool_settings
        b = ts.sculpt.brush
    except Exception:
        return "brush=?"
    if b is None:
        return "brush=?"
    parts = [f"brush={b.name}"]
    try:
        ups = ts.unified_paint_settings
    except Exception:
        ups = None
    for key, short in (("size", "size"), ("strength", "str")):
        val = None
        try:
            if ups is not None and getattr(ups, f"use_unified_{key}"):
                val = getattr(ups, key)
        except Exception:
            val = None
        if val is None:
            try:
                val = getattr(b, key)
            except Exception:
                val = None
        if val is not None:
            parts.append(f"{short}={num(val)}")
    try:
        d = b.direction
        if d:
            parts.append(f"dir={d}")
    except Exception:
        pass
    return " ".join(parts)


def sculpt_read():
    """Текущие локальные координаты вершин мешей в Sculpt Mode: {имя: array('f') длиной n*3}."""
    out = {}
    for obj in bpy.context.view_layer.objects:
        if obj.type != 'MESH' or obj.mode != 'SCULPT':
            continue
        n = len(obj.data.vertices)
        if n > MAX_SCULPT_VERTS:
            if obj.name not in _sculpt_warned:
                _sculpt_warned.add(obj.name)
                emit("SCULPT", f"{obj.name}: {n} вершин > MAX_SCULPT_VERTS={MAX_SCULPT_VERTS}, "
                               f"смещения не отслеживаются")
            continue
        try:
            arr = array('f', [0.0]) * (n * 3)
            obj.data.vertices.foreach_get("co", arr)
        except Exception:
            tmp = [0.0] * (n * 3)          # запасной путь: обычный список
            obj.data.vertices.foreach_get("co", tmp)
            arr = array('f', tmp)
        out[obj.name] = arr
    return out


def sculpt_reset():
    global _sculpt_last, _sculpt_quiet
    snap = sculpt_read()
    _sculpt_snap.clear()
    _sculpt_snap.update(snap)
    _sculpt_last = {}
    _sculpt_quiet = 0
    return snap


def sculpt_diff(new):
    """Сравнивает новые координаты со снимком. Возвращает список изменений по объектам."""
    res = []
    eps2 = MOVE_EPS * MOVE_EPS
    for name, cur in new.items():
        old = _sculpt_snap.get(name)
        if old is None:
            continue
        if len(old) != len(cur):
            res.append({"name": name, "kind": "topology", "a": len(old) // 3, "b": len(cur) // 3})
            continue
        if old == cur:          # быстрое сравнение массивов целиком: ничего не изменилось
            continue
        idx, dl = [], []
        for i in range(0, len(cur), 3):
            dx = cur[i] - old[i]
            dy = cur[i + 1] - old[i + 1]
            dz = cur[i + 2] - old[i + 2]
            if dx * dx + dy * dy + dz * dz > eps2:
                idx.append(i // 3)
                dl.append((dx, dy, dz))
        if idx:
            res.append({"name": name, "kind": "move", "n": len(cur) // 3, "idx": idx, "d": dl})
    return res


def emit_sculpt_changes(changes, tail):
    for ch in changes:
        name = ch["name"]
        if ch["kind"] == "topology":
            emit("VERTS", f"{name} число вершин {ch['a']}→{ch['b']} "
                          f"(топология изменилась, смещения не считаются){tail}")
            continue
        idx, dl = ch["idx"], ch["d"]
        items = [f"({i},{vec(d)})" for i, d in zip(idx, dl)]
        chunked("SCULPT", f"{name} Δ({len(idx)}/{ch['n']}){tail}", items)


def process_sculpt(prev, cur, op, params, adjusted, events):
    global _prev, _pending, _mode_op_wait, _sculpt_quiet, _sculpt_last
    mode_changed = cur["mode"] != prev["mode"]
    real_op = op is not None and not is_ignored(op_id(op))

    # вход в Sculpt Mode: пишем смену режима и делаем начальный снимок
    if mode_changed:
        _pending = 0
        _prev = cur
        _mode_op_wait = 0 if real_op else 20   # оператор смены режима может появиться на следующих тактах
        if real_op:
            n = push_step("act", op_id(op))
            emit_action(n, op, params, prev, cur)
        else:
            label = f"mode {prev['mode']}→{cur['mode']}"
            n = push_step("act", label)
            emit(f"ACT #{n}", label)
        snap = sculpt_reset()
        emit("SCULPT", "слежение за вершинами включено: "
             + (", ".join(f"{k} {len(v) // 3}v" for k, v in snap.items()) or "нет мешей"))
        return

    new = sculpt_read()
    changes = sculpt_diff(new)

    if DEBUG and (changes or op is not None or events):
        moved = sum(len(c.get("idx", ())) for c in changes)
        print(f"[DBG] sculpt: moved={moved} quiet={_sculpt_quiet} "
              f"op={op_id(op) if op is not None else None} events={events}")

    # Конец мазка = вершины перестали меняться. Операторы в истории для этого не нужны:
    # сначала ждём, пока изменения «успокоятся», потом записываем один мазок.
    if changes and not events and not real_op:
        if new == _sculpt_last:
            _sculpt_quiet += 1
        else:
            _sculpt_quiet = 0
        _sculpt_last = new
        if _sculpt_quiet < SCULPT_QUIET_TICKS:
            return
    _sculpt_quiet = 0
    _sculpt_last = {}
    _pending = 0
    _prev = cur

    if cur["settings"] and cur["settings"] != prev["settings"]:
        emit("SET", cur["settings"])
    if cur["tool"] and cur["tool"] != prev["tool"]:
        emit("TOOL", cur["tool"])

    if real_op and adjusted:
        events = []     # Adjust Last Operation делает Undo внутри себя, это не отмена пользователя

    # оператор смены режима, пришедший позже самой смены: уже записано как "mode A→B", дубль не пишем
    if _mode_op_wait > 0:
        _mode_op_wait -= 1
        if real_op and op_id(op) in MODE_OPS and not changes and not events:
            _mode_op_wait = 0
            _sculpt_snap.update(new)
            return

    tail = ""
    if real_op and adjusted:
        emit(f"ACT #{acts_applied()}", f"↻ параметры изменены: {op_id(op)} {params}")
    else:
        for e in events:
            emit_history(e)
        if events and not real_op:
            tail = " (undo/redo)"
        if real_op:
            oid = op_id(op)
            n = push_step("act", oid)
            line = oid
            b = brush_str()
            if b:
                line += " " + b
            if params:
                line += " " + params
            if not changes:
                line += " | вершины не изменились"
            emit(f"ACT #{n}", line)
        elif changes and not events:
            # мазок в историю операторов не попадает: имя дано по факту смещения вершин
            n = push_step("act", STROKE_LABEL)
            emit(f"ACT #{n}", f"{STROKE_LABEL} {brush_str()}")

    emit_sculpt_changes(changes, tail)
    _sculpt_snap.update(new)


# ---------- определение новых операторов ----------
def detect_new_op():
    """Возвращает (op, params, adjusted). adjusted=True: тот же оператор с изменёнными параметрами."""
    global _prev_ptrs, _prev_len, _last_ptr, _last_params
    ops = bpy.context.window_manager.operators
    n = len(ops)
    if n == 0:
        _prev_ptrs, _prev_len, _last_ptr, _last_params = set(), 0, None, None
        return None, None, False
    op = ops[n - 1]
    ptr = op.as_pointer()
    params = safe_params(op)
    adjusted = (ptr == _last_ptr) and params != _last_params
    new = (ptr not in _prev_ptrs) or (n > _prev_len) or adjusted
    _prev_ptrs = {o.as_pointer() for o in ops}
    _prev_len, _last_ptr, _last_params = n, ptr, params
    return (op, params, adjusted) if new else (None, None, False)


def modal_running():
    """True, пока выполняется модальный оператор (перемещение, поворот, экструд, мазок кисти...)"""
    global _dbg_modal
    names = []
    try:
        for w in bpy.context.window_manager.windows:
            for mop in w.modal_operators:
                if not is_ignored(op_id(mop)):
                    names.append(op_id(mop))
    except Exception:
        pass
    if DEBUG and bool(names) != _dbg_modal:
        _dbg_modal = bool(names)
        print(f"[DBG] modal_running={_dbg_modal} {names}")
    return bool(names)


# ---------- главный шаг ----------
def process():
    global _prev, _pending, _mode_op_wait
    if modal_running():
        return  # ждём завершения операции, состояние «до» не трогаем

    events = list(_events)
    _events.clear()
    cur = take_state()
    op, params, adjusted = detect_new_op()

    if _prev is None:
        _prev = cur
        emit("ACT", f"logger on | mode={cur['mode']}")
        if cur["settings"]:
            emit("SET", cur["settings"])
        if cur["tool"]:
            emit("TOOL", cur["tool"])
        emit_selection(cur)
        if cur["mode"] == "SCULPT":
            snap = sculpt_reset()
            emit("SCULPT", "слежение за вершинами включено: "
                 + (", ".join(f"{k} {len(v) // 3}v" for k, v in snap.items()) or "нет мешей"))
        return

    prev = _prev

    # ---- Sculpt Mode: отдельная ветка ----
    if cur["mode"] == "SCULPT":
        process_sculpt(prev, cur, op, params, adjusted, events)
        return
    if prev["mode"] == "SCULPT":
        _sculpt_snap.clear()

    mode_changed = cur["mode"] != prev["mode"]
    sel_changed = sel_sig(cur) != sel_sig(prev)
    real_op = op is not None and not is_ignored(op_id(op))

    # оператор смены режима, пришедший позже самой смены: уже записано как "mode A→B", дубль не пишем
    if mode_changed:
        _mode_op_wait = 0 if real_op else 20
    elif _mode_op_wait > 0:
        _mode_op_wait -= 1
        if real_op and op_id(op) in MODE_OPS and not sel_changed and not events:
            _mode_op_wait = 0
            _prev = cur
            return

    # ждём оператор только если изменилась топология (экструд, удаление...), обычный выбор пишем сразу
    if (op is None and not events and sel_changed and not mode_changed
            and (topo_changed(prev, cur) or prev["nobj"] != cur["nobj"])):
        _pending += 1
        if _pending < PENDING_TICKS:
            return
    _pending = 0
    _prev = cur

    if cur["settings"] and cur["settings"] != prev["settings"] and not mode_changed:
        emit("SET", cur["settings"])
    if cur["tool"] and cur["tool"] != prev["tool"] and not mode_changed:
        emit("TOOL", cur["tool"])

    if real_op and adjusted:
        events = []     # Adjust Last Operation делает Undo внутри себя, это не отмена пользователя

    if real_op:
        oid = op_id(op)
        if adjusted:
            # правка параметров через Adjust Last Operation: счётчик не растёт
            emit(f"ACT #{acts_applied()}", f"↻ параметры изменены: {oid} {params}")
        else:
            for e in events:          # настоящий Undo/Redo прямо перед новым действием
                emit_history(e)
            n = push_step("act", oid)
            emit_action(n, op, params, prev, cur)
    elif events:
        for e in events:
            emit_history(e)
    elif sel_changed:
        d = delta_str(prev, cur)
        if mode_changed:
            label = f"mode {prev['mode']}→{cur['mode']}"
            n = push_step("act", label)
            emit(f"ACT #{n}", label)
        elif d:
            n = push_step("act", "? правка без оператора")
            emit(f"ACT #{n}", "? правка без оператора | " + d)
        else:
            push_step("sel", sel_brief(cur))   # просто выбор: не действие, счётчик не меняется

    verts_change(prev, cur, bool(events))

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


def _remove_handlers():
    names = {"_on_depsgraph_update", "_on_undo_post", "_on_redo_post"}
    for lst_ in (bpy.app.handlers.depsgraph_update_post,
                 bpy.app.handlers.undo_post,
                 bpy.app.handlers.redo_post):
        for h in list(lst_):
            if getattr(h, "__name__", "") in names:
                lst_.remove(h)


def register():
    # --- убрать остатки прошлых версий скрипта ---
    _remove_handlers()
    for cls_name in ("MESH_OT_report_selected_verts_info", "WM_OT_act_logger_flush"):
        old = getattr(bpy.types, cls_name, None)
        if old is not None:
            try:
                bpy.utils.unregister_class(old)
            except Exception:
                pass

    bpy.utils.register_class(WM_OT_act_logger_flush)
    bpy.app.handlers.undo_post.append(_on_undo_post)
    bpy.app.handlers.redo_post.append(_on_redo_post)
    token = object()
    bpy.app.driver_namespace["act_logger_token"] = token
    bpy.app.timers.register(make_tick(token), first_interval=0.3, persistent=True)
    print("[ACT] Логирование действий включено")


def unregister():
    bpy.app.driver_namespace["act_logger_token"] = None
    _remove_handlers()
    try:
        bpy.utils.unregister_class(WM_OT_act_logger_flush)
    except Exception:
        pass
    print("[ACT] Логирование выключено")


register()
