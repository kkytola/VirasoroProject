#!/usr/bin/env python3
"""Parity check: old leanblueprint LaTeX vs new Verso blueprint sources.

Compares, per node label:
  - node kind (definition/lemma/theorem/...),
  - attached Lean declaration names,
  - statement-level `uses` edges,
  - proof presence and proof-level `uses` edges.

Old side:  blueprint/src/chapters/*.tex   (\\begin{kind}[title]\\label{..}\\uses{..}\\lean{..})
New side:  blueprint-verso/VirasoroBlueprint/Chapters/*.lean  (:::kind "label" (opts...) directives,
           with all options on the directive's opening line — the porting convention).

Exit code 0 iff full parity. Run from the repository root or blueprint-verso/.
"""

import re
import sys
from pathlib import Path
from dataclasses import dataclass, field


@dataclass
class Node:
    kind: str
    label: str
    lean: list = field(default_factory=list)
    uses: list = field(default_factory=list)
    has_proof: bool = False
    proof_uses: list = field(default_factory=list)


STMT_KINDS = ["definition", "lemma", "theorem", "proposition", "corollary", "remark"]


def _split_list(s):
    return [x.strip() for x in re.split(r"[,\n]", s) if x.strip()]


def parse_tex(chapter_dir: Path):
    nodes = {}
    order = []
    env_re = re.compile(
        r"\\begin\{(" + "|".join(STMT_KINDS) + r"|proof)\}(.*?)\\end\{\1\}", re.S
    )
    for tex in sorted(chapter_dir.glob("*.tex")):
        text = tex.read_text()
        # strip LaTeX comments (lines whose first non-space char is %), keep inline math intact
        text = "\n".join(l for l in text.splitlines() if not l.lstrip().startswith("%"))
        last_stmt = None
        for m in env_re.finditer(text):
            kind, body = m.group(1), m.group(2)
            get = lambda cmd: re.search(r"\\" + cmd + r"\{([^}]*)\}", body)
            if kind == "proof":
                if last_stmt is None:
                    print(f"WARN: proof without preceding statement in {tex.name}")
                    continue
                last_stmt.has_proof = True
                u = get("uses")
                if u:
                    last_stmt.proof_uses = _split_list(u.group(1))
            else:
                lab = get("label")
                if not lab:
                    print(f"WARN: {kind} without label in {tex.name}")
                    continue
                node = Node(kind=kind, label=lab.group(1).strip())
                u, l = get("uses"), get("lean")
                if u:
                    node.uses = _split_list(u.group(1))
                if l:
                    node.lean = _split_list(l.group(1))
                nodes[node.label] = node
                order.append(node.label)
                last_stmt = node
    return nodes, order


def parse_verso(chapter_dir: Path):
    nodes = {}
    order = []
    dir_re = re.compile(r'^:::(\w+)\s+"([^"]+)"(.*)$')
    opt_re = re.compile(r'\((\w+)\s*:=\s*"([^"]*)"\)')
    for lf in sorted(chapter_dir.glob("*.lean")):
        for line in lf.read_text().splitlines():
            m = dir_re.match(line.strip())
            if not m:
                continue
            kind, label, rest = m.group(1), m.group(2), m.group(3)
            opts = dict(opt_re.findall(rest))
            if kind == "proof":
                if label not in nodes:
                    print(f"WARN: proof for unknown statement {label!r} in {lf.name}")
                    continue
                nodes[label].has_proof = True
                if "uses" in opts:
                    nodes[label].proof_uses = _split_list(opts["uses"])
            elif kind.rstrip("_") in STMT_KINDS:
                node = Node(kind=kind.rstrip("_"), label=label)
                node.uses = _split_list(opts.get("uses", ""))
                node.lean = _split_list(opts.get("lean", ""))
                nodes[label] = node
                order.append(label)
    return nodes, order


def main():
    root = Path(__file__).resolve().parent.parent.parent
    old_dir = root / "blueprint" / "src" / "chapters"
    new_dir = root / "blueprint-verso" / "VirasoroBlueprint" / "Chapters"
    # Documented, deliberate corrections of defects in the old blueprint; see the
    # migration plan's "Pre-existing defects" list. Everything not listed here must
    # still match the old blueprint exactly.
    #
    # old label -> new label: `def:VirasoroVerma` was a typo in sugawara.tex for the
    # label actually defined in verma.tex.
    renames = {
        "def:VirasoroVerma": "def:VirasoroVermaModule",
    }
    # Nodes added on the Verso side that the old blueprint never defined.
    # `def:CyclicTripleSum` was cited by witt_cohomology.tex but defined nowhere.
    added_nodes = {
        "def:CyclicTripleSum",
    }
    # Lean names that never existed under the name the old blueprint used.
    lean_fixes = {
        "VirasoroProject.LieOneCochain.bdryHom": "VirasoroProject.LieOneCochain_bdryHom",
    }

    old, old_order = parse_tex(old_dir)
    new, new_order = parse_verso(new_dir)
    old = {renames.get(k, k): v for k, v in old.items()}
    for v in old.values():
        v.label = renames.get(v.label, v.label)
        v.uses = [renames.get(u, u) for u in v.uses]
        v.proof_uses = [renames.get(u, u) for u in v.proof_uses]
        v.lean = [lean_fixes.get(n, n) for n in v.lean]

    ok = True

    def err(msg):
        nonlocal ok
        ok = False
        print("MISMATCH:", msg)

    n_uses_old = sum(len(v.uses) + len(v.proof_uses) for v in old.values())
    n_uses_new = sum(len(v.uses) + len(v.proof_uses) for v in new.values())
    print(f"old: {len(old)} statements, {sum(v.has_proof for v in old.values())} proofs, "
          f"{sum(len(v.lean) for v in old.values())} lean refs, {n_uses_old} uses edges")
    print(f"new: {len(new)} statements, {sum(v.has_proof for v in new.values())} proofs, "
          f"{sum(len(v.lean) for v in new.values())} lean refs, {n_uses_new} uses edges")

    for lab in old:
        if lab not in new:
            err(f"node {lab!r} missing from Verso blueprint")
    for lab in new:
        if lab not in old and lab not in added_nodes:
            err(f"node {lab!r} not present in old blueprint")
    for lab in sorted(added_nodes & set(new)):
        print(f"NOTE: node added on the Verso side (documented): {lab}")
    for lab in sorted(set(old) & set(new)):
        o, n = old[lab], new[lab]
        if o.kind != n.kind:
            err(f"{lab}: kind {o.kind!r} -> {n.kind!r}")
        if sorted(o.lean) != sorted(n.lean):
            err(f"{lab}: lean {o.lean} -> {n.lean}")
        if sorted(o.uses) != sorted(n.uses):
            err(f"{lab}: statement uses {sorted(o.uses)} -> {sorted(n.uses)}")
        if o.has_proof != n.has_proof:
            err(f"{lab}: proof presence {o.has_proof} -> {n.has_proof}")
        if sorted(o.proof_uses) != sorted(n.proof_uses):
            err(f"{lab}: proof uses {sorted(o.proof_uses)} -> {sorted(n.proof_uses)}")

    old_dangling = {
        (lab, u)
        for lab, v in old.items()
        for u in v.uses + v.proof_uses
        if u not in old
    }
    new_dangling = {
        (lab, u)
        for lab, v in new.items()
        for u in v.uses + v.proof_uses
        if u not in new
    }
    for lab, u in sorted(new_dangling - old_dangling):
        err(f"{lab}: uses edge to undefined label {u!r}")
    for lab, u in sorted(new_dangling & old_dangling):
        print(f"NOTE: pre-existing dangling edge kept verbatim: {lab} -> {u!r}")

    print("PARITY OK" if ok else "PARITY FAILED")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
