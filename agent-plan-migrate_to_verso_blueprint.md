# Migration plan: `leanblueprint` (plasTeX) → Verso blueprint

**Status:** implemented through Phase 5 (2026-07-28); Phase 6 (decommission) deferred
until the first green Pages deployment, per §10. See "Implementation record" at the
end of this file for resolved open questions and documented deviations.
**Audience:** a coding agent (orchestrator) and its subagents.
**Repo:** `VirasoroProject` (Lean 4 formalization of Virasoro-algebra topics, depends on Mathlib).

---

## 0. Executive summary

This repository currently builds its formalization blueprint with Patrick Massot's
[`leanblueprint`](https://github.com/PatrickMassot/leanblueprint) (LaTeX sources under
`blueprint/src/`, compiled by plasTeX + LaTeX in CI, deployed to GitHub Pages alongside a
Jekyll home page and doc-gen4 API docs). The modern replacement is
[`leanprover/verso-blueprint`](https://github.com/leanprover/verso-blueprint) ("Verso
Blueprint"): blueprints are written as Verso documents in `.lean` files, the site is built
by `lake exe vbp build`, Lean declarations are linked natively (no `checkdecls`, no
plasTeX, no Python), and formalization status (`\leanok`) is **computed automatically**
from the Lean code instead of hand-maintained.

The migration is deliberately incremental:

1. **Phase 0** — baseline: move toolchain `v4.32.0-rc1` → `v4.32.0`, verify green build.
2. **Phase 1** — scaffold a new Lake subpackage `blueprint-verso/` from the upstream
   `project_template`, port one small pilot chapter, and resolve the listed open questions.
3. **Phase 2** — port the LaTeX macro vocabulary to a `tex_prelude`.
4. **Phase 3** — port the remaining 7 chapters (fan out: one subagent per chapter).
5. **Phase 4** — machine-checked parity verification against the old blueprint
   (node/edge/status counts).
6. **Phase 5** — rewrite CI (`.github/workflows/blueprint.yml`), update `home_page/` and
   `README.md` links, deploy.
7. **Phase 6** — decommission the plasTeX blueprint and `checkdecls`.

The old blueprint stays fully intact and deployed until Phase 5 succeeds; rollback at any
point is `git revert` plus keeping the old workflow.

---

## 1. Current state (inventory — verified 2026-07-27)

### 1.1 Blueprint sources

```
blueprint/src/
├── web.tex            # web driver: \documentclass{report}, \usepackage[showmore,dep_graph]{blueprint}
│                      #   \home{...kkytola.github.io/VirasoroProject} \github{...} \dochome{.../docs}
├── print.tex          # pdf driver (xelatex via latexmkrc)
├── content.tex        # 8 \chapter{...} + \input{chapters/*.tex}
├── chapters/          # the actual mathematical content, 1309 lines total:
│   ├── introduction.tex          (1 line: "\emph{Under construction.}")
│   ├── lie_algebra_cohomology.tex (162 ln)
│   ├── central_extension.tex      (169 ln)
│   ├── witt_cohomology.tex        (315 ln)
│   ├── virasoro_algebra.tex       (32 ln)   ← smallest real chapter, good pilot
│   ├── heisenberg_algebra.tex     (65 ln)
│   ├── verma.tex                  (152 ln)
│   └── sugawara.tex               (382 ln)
├── macros/common.tex  # ~40 \newcommand math macros (\bbk, \witt, \vir, \hei, \Loper, …) + theorem envs
├── macros/web.tex     # empty (comments only)
├── macros/print.tex   # dummy no-op defs of \lean, \leanok, \uses, \proves, \mathlibok, …
├── plastex.cfg, blueprint.sty, latexmkrc, extra_styles.css
```

### 1.2 Content statistics (what must be ported)

| Construct | Count | Notes |
|---|---|---|
| `\begin{definition}` | 24 | many with `[Title]` bracket titles |
| `\begin{lemma}` | 27 | |
| `\begin{theorem}` | 2 | |
| `\begin{proof}` | 29 | attach to preceding statement |
| `\lean{...}` | 53 | every statement node is Lean-linked; some list 2+ decls |
| `\leanok` | 82 | on statements *and* proofs → becomes automatic in Verso |
| `\uses{...}` | 81 | dependency edges (statement-level and proof-level) |
| `\ref{def:…}/\ref{lem:…}/\ref{thm:…}` | 39 | prose cross-references |
| `\begin{align*}` | 72 | display math |
| `\begin{align}` (numbered) | 5 | 3 carry `\label{eq:…}`; **`eq:LieTwoCocycle.leibniz` is defined in TWO files** (lie_algebra_cohomology.tex:39 and witt_cohomology.tex:105 — a latent duplicate-label bug; rename one during port) |
| `\begin{cases}` | 3 | inside display math, KaTeX/MathJax-safe |
| `\term{...}` | 22 | `\textbf` wrapper → markdown bold |
| `\emph{...}` | 1 | |
| `\cite` / bibliography | 0 | **no bibliography — one less thing to port** |
| `\mathlibok`, `\notready`, `\proves`, `\discussion` | 0 uses | defined in macros but never used |

Label conventions: `def:CamelCase`, `lem:CamelCase`, `thm:…`, `eq:…` — labels contain
colons and dots. Keep them verbatim if verso-blueprint accepts them (see Q3 in §4.4).

### 1.3 Build & deployment today

- `lakefile.toml`: requires `mathlib` (manifest pins a `master` commit), `checkdecls`
  (Massot), `doc-gen4` (`rev = "main"`, currently **not** pulling verso transitively).
- `lean-toolchain`: `leanprover/lean4:v4.32.0-rc1`.
- `.github/workflows/blueprint.yml` (single workflow, deploys everything):
  1. `lake exe cache get`; `lake build VirasoroProject`
  2. `lake -R -Kenv=dev build VirasoroProject:docs` (doc-gen4, with `.lake/build/doc` cache)
  3. texlive docker (`xu-cheng/texlive-action`): `pip install leanblueprint`;
     `leanblueprint pdf` → `home_page/blueprint.pdf`; `leanblueprint web` → `home_page/blueprint/`
  4. `lake exe checkdecls blueprint/lean_decls`
  5. copy API docs → `home_page/docs`; Jekyll build of `home_page/`; deploy to Pages.
- `home_page/index.md` links: `/blueprint/`, `/blueprint.pdf`,
  `/blueprint/dep_graph_document.html`, `/docs/`.
- Published at <https://kkytola.github.io/VirasoroProject> (also linked from `README.md`).

---

## 2. Target system: Verso Blueprint essentials

Primary resources (read these before implementing; fetch on the **`v4.32.0` branch**, not `main`):

| Resource | URL |
|---|---|
| Package repo (branch **`v4.32.0`**) | <https://github.com/leanprover/verso-blueprint/tree/v4.32.0> |
| Getting started | `doc/GETTING_STARTED.md` in that repo |
| Authoring manual | `doc/MANUAL.md` |
| API reference | `doc/API.md` |
| Starter template | `project_template/` (copy-adapt source for Phase 1) |
| **Agent skill** shipped upstream | `skills/verso-blueprint/` — read it; it is written for coding agents doing exactly this kind of work |
| Porting methodology (battle-tested on FLT, Carleson, Sphere Packing, Noperthedron) | <https://github.com/ejgallego/leanblueprint-to-verso> — esp. `references/porting.md`, `references/lt-method.md`, `references/retrofit.md` |
| Worked reference ports (mathlib-heavy) | <https://github.com/ejgallego/verso-noperthedron>, `verso-flt`, `verso-carleson`, `verso-sphere-packing` |

Key facts:

- **Toolchain coupling.** verso-blueprint publishes one branch per Lean release line:
  `v4.28.0` … `v4.32.0`. The blueprint package's toolchain must match the branch. Our
  project must therefore sit on `leanprover/lean4:v4.32.0` (stable) and require
  `VersoBlueprint from git "https://github.com/leanprover/verso-blueprint" @ "v4.32.0"`.
- **Documents are Lean files.** A chapter is a module starting `#doc (Manual) "Title" =>`.
  A top-level `Blueprint.lean` assembles chapters with `{include 0 Pkg.Chapters.Foo}` and
  adds overview pages via `{blueprint_graph}` and `{blueprint_summary}` (graph options:
  `(direction := LR|RL|TB|BT)`, `(pack := …)`, `(preview := pinned|hover)`).
- **Nodes** are directives with stable string labels:
  `:::definition "label"`, `:::lemma_ "label"` (note the underscore — `lemma` is taken),
  `:::theorem`, `:::proposition`, `:::corollary`, `:::remark`, and `:::proof "label"`
  (same label as its statement). Options: `(lean := "Foo.bar, Foo.baz")`,
  `(uses := "lbl1, lbl2")`, `(owner := …)`, `(tags := …)`, `(priority := …)`,
  `(effort := …)`, `(autoDeps := true|false)`.
- **Status is automatic.** There is no `\leanok`. A node linked to Lean code (via
  `(lean := …)`, a labeled ```` ```lean "label" ```` block, or the `@[blueprint "label"]`
  attribute on a declaration) gets its status computed from the elaborated code
  (sorry-free ⇒ formalized). This also **replaces `checkdecls`**: a bad name in
  `(lean := …)` fails the build.
- **Math**: inline ``$`n + 0 = n` ``, display ``$$`\sum_{i=0}^{n} i` ``. Custom macros go
  in a TeX prelude: `tex_prelude r#"\newcommand{\witt}{\mathfrak{witt}}"#`.
- **Prose cross-reference without a dependency edge**: `{bpref "def:WittAlgebra"}[]`.
  In-prose dependency chip: `{uses "label"}[]`.
- **Porting escape hatch (LT method)**: labeled/unlabeled ```` ```tex ```` blocks can hold
  the original LaTeX next to its translation as a "witness"
  (` ```tex "label" (slot := statement) … ``` `). Use these during the port for
  reviewability; prune later (§8).
- **Build**: `lake exe vbp build` → HTML site at `_out/site/html-multi/`;
  `--serve` for local preview; `--pdf` (needs `lualatex`; `--pdf-engine <cmd>` to
  override) → `_out/site/pdf/main.pdf`; `--output <dir>` supported (verify exact
  semantics with `lake exe vbp build --help`).
  Metadata export for scripted checks: `lake exe vbp query metadata`,
  `lake exe vbp query work-queue`.
- Template lakefile pattern (v4.32.0):

  ```lean
  import Lake
  open Lake DSL

  require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint"@"v4.32.0"
  package ProjectTemplate where
    precompileModules := false
    leanOptions := #[⟨`experimental.module, true⟩]

  @[default_target]
  lean_lib ProjectTemplate where
  ```

  and generator entry point:

  ```lean
  import VersoManual
  import VersoBlueprint.PreviewManifest
  import ProjectTemplate.Blueprint

  open Verso Doc
  open Verso.Genre Manual

  def main (args : List String) : IO UInt32 :=
    Informal.PreviewManifest.blueprintMainWithPreviewData
      (%doc ProjectTemplate.Blueprint)
      args
      (extensionImpls := by exact extension_impls%)
  ```

(Related but distinct: the arXiv paper 2601.22554 "LeanArchitect" (Zhu, Monticone,
Avigad, Welleck) automates blueprint generation from Lean code — background reading, not
part of this migration.)

---

## 3. Architecture decision

**Decision: in-repo Lake subpackage `blueprint-verso/` that path-requires the root
package** (Mathlib's `docbuild/` pattern). Rationale:

- The main formalization package stays clean: `VersoBlueprint` (which vendors Verso) is
  **not** added to the root `lakefile.toml`, so no risk of dependency clashes with
  `doc-gen4`/Mathlib for downstream users, and no rebuild pressure on the formalization.
- Chapters can `import VirasoroProject.WittAlgebra` etc., which is required for
  `(lean := "VirasoroProject.…")` references to resolve.
- Single repo, single Pages site — unlike the upstream "reference ports"
  (`ejgallego/verso-flt` etc.), which are *separate wrapper repos* because they don't own
  the upstream formalization. We own both halves, so in-repo is simpler.
- The `ejgallego/leanblueprint-to-verso` harness (git submodule `tools/verso-harness`,
  `verso-harness.toml`, audit scripts) is designed for maintaining *fleets* of wrapper
  ports. For a single 1300-line blueprint, adopting the submodule is overkill —
  **borrow its methodology** (`references/porting.md`, LT witnesses, incremental batches)
  without the machinery. Revisit if maintenance burden grows.

Target layout after migration:

```
VirasoroProject/                      # root package: unchanged (mathlib, doc-gen4; checkdecls removed in Phase 6)
├── lean-toolchain                    # leanprover/lean4:v4.32.0   (bumped in Phase 0)
├── VirasoroProject/…                 # formalization, untouched
├── blueprint-verso/                  # NEW Lake package
│   ├── lakefile.lean
│   ├── lake-manifest.json
│   ├── VirasoroBlueprint.lean        # `import VirasoroBlueprint.Blueprint`
│   ├── VirasoroBlueprintMain.lean    # generator entry point
│   └── VirasoroBlueprint/
│       ├── Blueprint.lean            # #doc top level: includes + {blueprint_graph} + {blueprint_summary}
│       ├── TeXPrelude.lean           # tex_prelude with macros from macros/common.tex
│       └── Chapters/
│           ├── Introduction.lean
│           ├── LieAlgebraCohomology.lean
│           ├── CentralExtension.lean
│           ├── WittCohomology.lean
│           ├── VirasoroAlgebra.lean
│           ├── HeisenbergAlgebra.lean
│           ├── Verma.lean
│           └── Sugawara.lean
├── home_page/                        # Jekyll site, kept; links updated
└── .github/workflows/blueprint.yml   # rewritten (Phase 5)
```

`blueprint-verso/lakefile.lean` (to be validated in Phase 1):

```lean
import Lake
open Lake DSL

require VirasoroProject from ".."
require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint"@"v4.32.0"

package VirasoroBlueprint where
  precompileModules := false
  leanOptions := #[⟨`experimental.module, true⟩]

@[default_target]
lean_lib VirasoroBlueprint where
```

No `lean-toolchain` inside `blueprint-verso/` — elan resolves the root one (verify; if
lake complains, symlink or copy the root file and add a CI consistency check).

---

## 4. Phase 0 — baseline and toolchain (single agent, blocking)

1. `lake build VirasoroProject` on the current state; record result. (Recent history
   contains "Bump to v4.32.0-rc1 --- with possibly dubious proof repairs" — if the build
   is red, fix that **first**, as its own task; do not mix with the migration.)
2. Bump `lean-toolchain` to `leanprover/lean4:v4.32.0` (stable) and update the Mathlib pin
   to the matching release (`lake update mathlib` after setting the version, or pin
   Mathlib's `v4.32.0` tag). Rationale: verso-blueprint's `v4.32.0` branch is built and
   tested against stable v4.32.0; keeping the whole repo on one toolchain avoids
   cross-toolchain `.olean` mismatches between the root package and the blueprint package.
3. While editing `lakefile.toml`, pin `doc-gen4` to the currently working manifest
   revision instead of `rev = "main"` (a floating `main` is a standing CI risk and, if
   doc-gen4 ever grows a Verso dependency, a version-clash risk with `blueprint-verso`).
4. `lake exe cache get && lake build VirasoroProject` must be green. Commit as its own PR
   before any blueprint work.

**Fallback** if v4.32.0-stable bump turns out to be costly: verso-blueprint's test matrix
also exercises rc toolchains (`4.32-rc1` appears in `tests/harness/projects.json`), so
staying on `v4.32.0-rc1` and requiring the `v4.32.0` branch *may* work — treat as plan B,
verify in the Phase 1 spike.

---

## 5. Phase 1 — scaffold + pilot chapter (single agent)

1. Fetch the upstream template: sparse-clone `leanprover/verso-blueprint` at branch
   `v4.32.0`, copy `project_template/` → `blueprint-verso/`, then rename
   `ProjectTemplate*` → `VirasoroBlueprint*` throughout (files, module names, lakefile
   package/lib names, `%doc` reference in the Main file). Read
   `project_template/README.md` and `skills/verso-blueprint/` **before** editing.
2. Delete the template's example chapters; create
   `VirasoroBlueprint/Chapters/VirasoroAlgebra.lean` as the **pilot** (port of
   `blueprint/src/chapters/virasoro_algebra.tex` — 32 lines, 2 nodes) plus a stub
   `Introduction.lean` (`\emph{Under construction.}` → *Under construction.*).
3. Write `Blueprint.lean`:

   ```lean
   #doc (Manual) "The Virasoro Project blueprint" =>

   {include 0 VirasoroBlueprint.Chapters.Introduction}
   {include 0 VirasoroBlueprint.Chapters.VirasoroAlgebra}
   -- …remaining chapters appended in Phase 3…

   # Dependency graph
   {blueprint_graph}

   # Progress
   {blueprint_summary}
   ```

   (Exact placement/headers: imitate the template's `Blueprint` module.)
4. Build: `cd blueprint-verso && lake update && lake exe vbp build`. First build compiles
   Verso + elaborates VirasoroProject imports; expect it to be slow once, then cached.
5. Preview locally with `lake exe vbp build --serve`; sanity-check rendering, the two
   pilot nodes, their Lean links, and the graph page. Record the **actual dependency-graph
   page path** in the built site (needed for `home_page/index.md` in Phase 5).

### 4.4 Open questions the pilot MUST answer (record answers in this file)

- **Q1 — parent path-require works?** `require VirasoroProject from ".."` with a TOML
  parent lakefile. Expected yes (Mathlib `docbuild/` precedent). Fallback: git-require the
  repo itself (ugly) or convert root lakefile to `.lean`.
- **Q2 — `experimental.module` interplay**: template sets `experimental.module := true`
  for the *blueprint* package while importing non-module VirasoroProject/Mathlib code.
  Expected fine (options are per-package); if not, drop the option and check what breaks.
- **Q3 — labels with `:` and `.`** (`def:WittAlgebra`, `eq:LieTwoCocycle.self`): accepted
  by node directives, `uses`, `bpref`? (Upstream JS example uses
  `"Chapter2:Problem2.11.6"`, so likely yes.) Fallback: global rename `:`→`_` — do it
  mechanically and consistently in one commit.
- **Q4 — titled statements**: LaTeX had `\begin{definition}[Witt algebra]`. The manual
  lists no `(title := …)` option. Check `doc/MANUAL.md` again + reference ports
  (`verso-noperthedron`) for the idiom. Fallback: start the body with `**Witt algebra.**`
  (bold run-in title), consistently.
- **Q5 — `align*`/numbered `align` in display math**: does
  ``$$`\begin{align*} … \end{align*}` `` render? (Depends on the math engine's
  environment support.) Fallback: convert to `\begin{aligned}…\end{aligned}` inside
  `$$`…`` (drop per-line numbering; the 3 `eq:` labels are referenced nowhere via
  `\ref{eq:…}` in chapters — verified: all 39 refs are `def:`/`lem:`/`thm:` — so
  numbering loss is cosmetic).
- **Q6 — `--output` flag semantics** for CI (`lake exe vbp build --help`).
- **Q7 — PDF build**: does `lake exe vbp build --pdf` succeed locally with `lualatex`?
  (The old PDF used xelatex; expect font/format differences — acceptable.)

Commit Phase 1 as one PR ("verso blueprint scaffold + pilot chapter"), leaving the old
blueprint untouched.

---

## 6. Phase 2 — TeX prelude (macros)

Port `blueprint/src/macros/common.tex` into `VirasoroBlueprint/TeXPrelude.lean` as
`tex_prelude r#"…"#` block(s), imported by every chapter (imitate how the template/
manual wires the prelude in).

- Port **only math-mode macros** (`\bN…\bC`, `\bbk`, `\gLie`, `\aLie`, `\egLie`, `\hei`,
  `\witt`, `\vir`, `\UEA`, `\Joper`, `\Loper`, `\Verma`, `\VermaHWV`, `\FockSpace`,
  `\FockVacuum`, `\id`, `\idOf`, `\indicator`, `\Ima`, `\Ker`, `\Coc`, `\Coch`, `\Cob`,
  `\Coh`, `\normalOrder`, `\tagHeiComm`, `\tagHeiTrunc`).
- Do **not** port `\term` (text-mode; becomes markdown `**bold**`) or the
  `\newtheorem` setup (superseded by node directives).
- ⚠️ `\normalOrder` expands to `{\mathbb{:} #1 \mathbb{:}}` — `\mathbb` applied to a colon
  is dubious even in LaTeX; test its rendering explicitly and, if broken, redefine (e.g.
  `{:} #1 {:}` or `\mathop{:}…`) — visual change is acceptable, macro name must stay.
- Verify each macro renders by adding a temporary "macro zoo" test section during
  development (delete before merge), or rely on the pilot + chapter builds.

---

## 7. Phase 3 — port the remaining chapters (parallel subagents)

Fan out **one subagent per chapter** (7 remaining: `lie_algebra_cohomology`,
`central_extension`, `witt_cohomology`, `heisenberg_algebra`, `verma`, `sugawara`, and
finishing `introduction`). Chapters only reference each other through labels, and the
generator resolves forward references, so chapters are independent and parallelizable;
each writes exactly one new file — no merge conflicts. The orchestrator appends the
`{include 0 …}` lines to `Blueprint.lean` and runs the integration build afterwards.

**Each subagent receives:** this section (§7) + the conversion table below + the pilot
chapter file as a style reference + its source `.tex` path + target module path.

### 7.1 Conversion table (this repo's idioms)

| LaTeX (source) | Verso (target) |
|---|---|
| `\chapter{X}` + `\input{chapters/y.tex}` (in content.tex) | chapter module `#doc (Manual) "X" =>` + `{include 0 …}` in `Blueprint.lean` |
| `\section{Foo}` | Verso section header inside the module (imitate template chapters — `# Foo` style header) |
| `\begin{definition}[T]\label{def:X} … \end{definition}` | `:::definition "def:X" (…)` … `:::` (title per Q4 resolution) |
| `\begin{lemma}…` | `:::lemma_ "lem:X"` — **note trailing underscore** |
| `\begin{theorem}…` | `:::theorem "thm:X"` |
| `\begin{proof}` after statement `L` | `:::proof "L"` … `:::` (same label as the statement) |
| `\lean{A, B}` (in statement) | `(lean := "A, B")` on the statement directive |
| `\leanok` | **delete** — status is computed |
| `\uses{a, b}` in a statement | `(uses := "a, b")` on the statement directive |
| `\uses{a, b}` in a proof | `(uses := "a, b")` on the `:::proof` directive |
| `Definition~\ref{def:X}` / `Lemma~\ref{lem:Y}` | `{bpref "def:X"}[]` (renders as "Definition N"; do **not** use `{uses …}` for mere prose references — `uses` creates graph edges) |
| `$…$` | ``$`…` `` |
| `\begin{align*}…\end{align*}` | ``$$`…` `` display block, per Q5 resolution (likely `\begin{aligned}`) |
| `\begin{align}\label{eq:…}` (5 occurrences) | same as align*; drop the number/label (no `\ref{eq:…}` exists); **rename** the duplicated `eq:LieTwoCocycle.leibniz` if labels are kept anywhere |
| `\term{X}` | `**X**` |
| `\emph{X}` | `*X*` |
| `%`-comments | drop, or keep as Lean `--` comments outside directives if genuinely informative |
| commented-out `\uses{}` (e.g. `%\uses{}`) | drop |

**Fidelity rules** (from upstream `references/porting.md`):

- Preserve section order, node order, statement wording, and math **verbatim** — this is
  a port, not a rewrite. No new prose, no dropped sentences (log any forced deviation in
  the PR description).
- Preserve environment kinds exactly (a lemma stays `lemma_`, never flattened to
  `theorem`).
- Keep every label verbatim (mod the Q3 fallback), keep every `uses` edge exactly as the
  TeX had it — no invented or "obviously missing" edges; those are follow-up curation,
  not porting.
- Do not use `autoDeps`, `uses_intent`, `uses_origin` during the port.
- **LT witness (recommended)**: below each ported node, keep the original LaTeX in an
  unlabeled ```` ```tex ```` block during review. These make the parity review trivial
  and are pruned in Phase 6. If they turn noisy, at minimum keep them for `sugawara.tex`
  and `witt_cohomology.tex` (the two big chapters).

### 7.2 Worked example (from `witt_cohomology.tex`)

LaTeX source:

```latex
\begin{lemma}[Witt algebra is a Lie algebra]
  \label{lem:WittAlgebraIsLieAlgebra}
  \uses{def:WittAlgebra}
  \lean{VirasoroProject.WittAlgebra.instLieAlgebra}
  \leanok
  If $\bbk$ is a field of characteristic zero, then $\witt$ is
  a Lie algebra over $\bbk$. …
\end{lemma}
\begin{proof}
  \uses{def:CyclicTripleSum}
  \leanok
  By construction, the bracket in Definition~\ref{def:WittAlgebra} is bilinear. …
\end{proof}
```

Verso target (title idiom pending Q4):

````
:::lemma_ "lem:WittAlgebraIsLieAlgebra" (uses := "def:WittAlgebra") (lean := "VirasoroProject.WittAlgebra.instLieAlgebra")
**Witt algebra is a Lie algebra.**
If $`\bbk` is a field of characteristic zero, then $`\witt` is
a Lie algebra over $`\bbk`. …
:::

:::proof "lem:WittAlgebraIsLieAlgebra" (uses := "def:CyclicTripleSum")
By construction, the bracket in {bpref "def:WittAlgebra"}[] is bilinear. …
:::
````

### 7.3 Per-chapter checklist (subagent exit criteria)

- [ ] Node count and kinds match the source `.tex` exactly (definitions/lemmas/theorems/proofs).
- [ ] All `\lean{}` names carried over; chapter module imports the needed
      `VirasoroProject.*` modules (narrowest imports that make names resolve).
- [ ] All `\uses{}` edges carried over to the right directive (statement vs proof).
- [ ] All `\ref{}`s became `bpref`s.
- [ ] `lake build VirasoroBlueprint` (or the module) succeeds from `blueprint-verso/`.
- [ ] No leftover raw LaTeX outside witness blocks (`grep -n '\\begin\|\\uses\|\\lean{\|\\leanok\|\\ref{' file` in non-witness lines is empty).

---

## 8. Phase 4 — parity verification (single agent)

1. Full build: `cd blueprint-verso && lake exe vbp build` (and `--pdf` if Q7 was green).
2. **Automated parity check** — write
   `blueprint-verso/scripts/parity_check.py` (throwaway, keep in repo until Phase 6):
   - Parse old TeX (`blueprint/src/chapters/*.tex`) with regexes for
     `\begin{(definition|lemma|theorem|proof)}`, `\label`, `\lean`, `\uses` →
     old node set + edge set. Expected totals from §1.2: 53 statements, 29 proofs,
     53 lean-links, 81 uses-edges.
   - Read the new metadata: `lake exe vbp query metadata` (JSON; see `doc/API.md` for
     shape) → new node set + edge set + statuses.
   - Assert: label sets equal (mod documented renames), kinds equal, per-node lean-name
     multisets equal, per-node uses-sets equal.
   - Assert status: the project builds sorry-free, and the old blueprint marked
     essentially everything `\leanok`, so every lean-linked node should report a
     fully-formalized status; `lake exe vbp query work-queue` should be (near-)empty.
     Investigate every discrepancy — each one is either a port bug or a real insight
     (e.g. a stale `\leanok` in the old blueprint); log which.
3. Visual checks: dependency graph old
   (`…/blueprint/dep_graph_document.html`) vs new graph page — same component structure;
   spot-check 3 nodes per chapter for math rendering (especially `aligned` conversions,
   `cases`, `\normalOrder`).
4. Fix-forward until parity_check passes.

---

## 9. Phase 5 — CI, home page, deployment (single agent)

Rewrite `.github/workflows/blueprint.yml` (keep the job skeleton: checkout, elan,
`lake exe cache get`, `lake build VirasoroProject`, doc-gen4 step + its cache, Jekyll,
upload-pages-artifact, deploy-pages). Replace the blueprint-specific middle:

**Remove:** the `xu-cheng/texlive-action` docker step (plasTeX/`leanblueprint` pip
build), and the `lake exe checkdecls blueprint/lean_decls` step.

**Add** (after the formalization build so `../.lake` is warm):

```yaml
      - name: Build verso blueprint
        working-directory: blueprint-verso
        run: |
          ~/.elan/bin/lake update VersoBlueprint || true   # only if needed; prefer committed manifest
          ~/.elan/bin/lake exe vbp build
          mkdir -p ../home_page
          cp -r _out/site/html-multi ../home_page/blueprint
```

- Cache `blueprint-verso/.lake` keyed on `blueprint-verso/lake-manifest.json` +
  `lean-toolchain` (Verso compilation is the expensive part; upstream's reusable
  `project_template/.github/workflows/blueprint-pages.yml` shows the 3-layer cache
  pattern — Lake packages / root build / formalization build — copy it).
- **PDF** (optional, can ship in a follow-up): install a LuaLaTeX texlive
  (`apt-get install -y texlive-luatex texlive-latex-extra texlive-fonts-recommended` or
  keep the texlive docker for just this), run `lake exe vbp build --pdf`, copy
  `_out/site/pdf/main.pdf` → `home_page/blueprint.pdf`. Until then, drop the PDF link
  from `home_page/index.md` rather than serving a stale file.
- Note: upstream's reusable workflow assumes the blueprint *is* the whole Pages site; we
  keep our composite site (Jekyll + `/docs` + `/blueprint`), hence the custom workflow.

**Update links:**

- `home_page/index.md`: `/blueprint/` stays; dependency-graph link
  `/blueprint/dep_graph_document.html` → the new graph page path recorded in Phase 1;
  PDF link per above.
- `README.md`: unchanged top link; skim for any deep blueprint URLs.

**Cutover:** merge; watch the Pages deployment; click through home page → blueprint →
graph → summary → a few Lean-decl links → `/docs/`. Old URLs that die
(`dep_graph_document.html`) are acceptable; the top-level `/blueprint/` URL must keep
working.

---

## 10. Phase 6 — decommission (single agent, after ≥1 green deployment)

1. Delete `blueprint/` (plasTeX tree). It stays in git history; no archival copy needed.
   ⚠️ This is `blueprint/` at repo root only — do **not** touch `VirasoroProject/ToMathlib/`
   (repo policy: ToMathlib ledger files are never deleted).
2. Remove the `checkdecls` require from `lakefile.toml` (its job — validating `\lean{}`
   names — is now done by the blueprint package's elaboration) and drop any remaining
   references to `blueprint/lean_decls`.
3. Prune or keep LT witness blocks (team choice; default: prune, since git history and
   the parity report preserve the mapping). Delete `parity_check.py` or move it under a
   `scripts/` attic.
4. Update this plan file's Status line to "implemented"; note deviations inline.
5. Optional follow-ups (explicitly out of scope for the migration itself):
   - Restyle via verso-blueprint's static-web hooks (the old `extra_styles.css` border
     styling is dropped — the Verso theme has its own look).
   - Adopt `@[blueprint "label"]` attributes in the Lean source and/or `autoDeps` to
     reduce duplication — *curation*, after the faithful port has landed.
   - Add `owner`/`priority`/`effort` metadata to open nodes (the "Under construction"
     introduction suggests more chapters are coming).

---

## 11. Risks and mitigations

| Risk | Mitigation |
|---|---|
| Toolchain bump v4.32.0-rc1→v4.32.0 breaks proofs (rc1 bump was already "dubious") | Phase 0 is isolated and lands first; plan B: stay on rc1 (tested in upstream harness matrix) |
| `require VirasoroProject from ".."` unsupported quirk | Q1 pilot check; fallbacks listed |
| `doc-gen4 @ main` someday requires Verso → version clash in the *root* package | doc-gen4 pinned in Phase 0; if a clash ever appears, split doc-gen4 into a `docbuild/` subpackage (Mathlib pattern) |
| Labels with `:`/`.` rejected | Q3; mechanical rename fallback |
| `align*`/`cases`/`\mathbb{:}` render badly in the Verso math engine | Q5 + §6 macro zoo; `aligned` fallback; redefine `\normalOrder` |
| Statement titles unsupported | Q4; bold run-in fallback |
| First CI build extremely slow (compiles Verso + full project under new package) | `.lake` caching keyed on manifest; upstream 3-layer cache pattern |
| PDF regression (xelatex → lualatex, different template) | PDF is a stretch goal; drop the link until `--pdf` output is acceptable |
| Silent content drift during port | LT witness blocks + Phase 4 automated parity check (node/edge/lean-name sets, not eyeballs) |

---

## 12. Orchestration summary for the implementing agent

- Phases 0→1→2 are sequential, single-agent (Phase 1 resolves Q1–Q7; **update §4.4 with
  the answers before fanning out**).
- Phase 3: launch 7 parallel subagents (one chapter each; they share §7 + the pilot file;
  each touches exactly one new file). Orchestrator integrates includes + runs the build.
- Phases 4→5→6 sequential, each a separate PR; Phase 6 only after a green production
  deployment has been manually spot-checked.
- Suggested PR sequence: (1) toolchain baseline, (2) scaffold+pilot, (3) macros+chapters
  [+parity script], (4) CI+links cutover, (5) decommission.

---

## Implementation record (added 2026-07-28)

### Resolved open questions (§4.4)

- **Q1 — parent path-require:** YES. `require VirasoroProject from ".."` works with the
  TOML parent lakefile; VirasoroProject artifacts are reused from `../.lake/build`.
- **Q2 — `experimental.module`:** no interference with non-module VirasoroProject/Mathlib
  imports. Kept as in the template.
- **Q3 — labels with `:` and `.`:** fully supported (upstream `LabelNameParsing.lean`
  handles TeX-style labels explicitly; stored via `Name.mkSimple`, no dot-splitting).
  All labels kept verbatim.
- **Q4 — titled statements:** there is NO title option (full option list:
  `lean, autoDeps, parent, priority, owner, tags, effort, pr_url, uses, uses_origin,
  uses_intent`). Bracket titles became bold run-ins `*Title.*` as the first body line.
- **Q5 — display math:** `\begin{align*}` → `` $$`\begin{aligned}…\end{aligned}` ``
  (KaTeX renders the math, `throwOnError:false`). Numbered `align` treated the same;
  the 3 `eq:` labels dropped. NOTE (correction to §1.2/§7.1): two `\eqref`s DID exist
  in `lie_algebra_cohomology.tex`; the references were removed with the sentences kept
  meaningful (documented in that chapter's port).
- **Q6 — `--output <dir>`:** replaces `_out/site`; HTML lands under `<dir>/html-multi`.
  CI copies `_out/site/html-multi` → `home_page/blueprint` instead.
- **Q7 — PDF:** no LaTeX engine on the dev machine; `vbp build --pdf` (lualatex) is a
  `continue-on-error` step in CI — the HTML site deploys even if the PDF fails.

### Deviations from the plan

1. **Toolchain kept at `v4.32.0-rc1`** (plan B of §4) instead of bumping to stable:
   the baseline build was green with the existing cache, and VersoBlueprint@v4.32.0
   compiles fine under rc1. `blueprint-verso/lean-toolchain` pins rc1 explicitly
   (lake update had auto-written v4.32.0-stable, which broke the mathlib cache).
   `blueprint-verso/lake-manifest.json` was reconciled so that mathlib and friends
   match the root manifest exactly (lake had floated `plausible`; re-pinned).
2. **No LT witness blocks** (§7.1): parity is machine-checked directly against the
   LaTeX sources by `blueprint-verso/scripts/parity_check.py` (node kinds, labels,
   per-node lean-name multisets, statement/proof uses-edges), which supersedes the
   witness mechanism. PARITY OK: 53 statements / 29 proofs / 69 lean refs / 86
   uses-edges on both sides.
3. **Verso markup, not markdown**: bold is `*x*`, emphasis `_x_` (Verso linter).
   PORTING.md was corrected accordingly after the pilot build.
4. **Chapter imports** are per-module (`import VirasoroProject.WittAlgebra` etc.,
   narrowest set containing the referenced declarations) as the plan originally
   wanted, not the umbrella import PORTING.md temporarily suggested.

### Pre-existing defects in the OLD blueprint discovered by the port

1. `witt_cohomology.tex:34`: `\uses{def:CyclicTripleSum}` — label defined nowhere
   (dangling edge). Kept verbatim; parity script reports it as a NOTE.
2. `sugawara.tex:357`: `\uses{..., def:VirasoroVerma}` — typo for
   `def:VirasoroVermaModule`. Kept verbatim; NOTE in parity script.
3. `lie_algebra_cohomology.tex` / `central_extension.tex`:
   `\lean{VirasoroProject.LieOneCochain.bdryHom}` — the declaration is actually
   named `VirasoroProject.LieOneCochain_bdryHom` (underscore). The integration build
   warns ("could not be resolved") and would render a dead link, so the name was
   CORRECTED in the port (both occurrences); allowlisted in `parity_check.py`
   (`lean_fixes`).
4. Duplicate LaTeX label `eq:LieTwoCocycle.leibniz` in two files (§1.2) — moot in
   the port, since `eq:` labels are dropped.

### Status parity (Phase 4 result)

The generated graph has 55 nodes / 86 edges (53 real nodes + 2 phantoms for the
pre-existing dangling labels). Automatic status: 52/53 statements `formalized`,
proofs `formalized(WithAncestors)`. The single exception is
`thm:CentralExtensionOfCohomologyClass` (status `ready`): the old blueprint marked
it `\leanok` while its `\lean{}` was commented out — i.e. the old blueprint
over-claimed; Verso reports the honest status. Attaching the intended declaration
to that node is a content follow-up for the author, not part of the verbatim port.

Cosmetic note: node display labels render with guillemets («def:WittAlgebra») in
the graph UI, an artifact of Lean `Name` printing for labels containing `:`.
Harmless; could be polished later via the `verso.blueprint.trimTeXLabelPrefix`
option or a label rename if desired.
