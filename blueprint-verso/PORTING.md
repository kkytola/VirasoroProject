# Chapter porting conventions (leanblueprint LaTeX → Verso)

Reference for porting `blueprint/src/chapters/*.tex` to
`blueprint-verso/VirasoroBlueprint/Chapters/*.lean`. This is a **verbatim port**:
preserve section order, node order, statement wording, and math content exactly.
Do not add, drop, or "improve" prose, labels, `uses` edges, or `lean` references.

## Module skeleton

Every chapter module starts exactly like this (chapter title = the `\chapter{...}`
title from `blueprint/src/content.tex`):

```
import Verso
import VersoManual
import VersoBlueprint
import VirasoroProject.<ModulesContainingTheReferencedDecls>
import VirasoroBlueprint.TeXPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "<chapter title>" =>
```

## Structure mapping

| LaTeX | Verso |
|---|---|
| `\section{Foo}` | `# Foo` on its own line |
| `\begin{definition}[T] \label{L} \uses{U} \lean{N} \leanok BODY \end{definition}` | `:::definition "L" (uses := "U") (lean := "N")` ⏎ `*T.*` ⏎ `BODY` ⏎ `:::` |
| `\begin{lemma}...` | `:::lemma_ "L" ...` — **note the trailing underscore, only for lemma** |
| `\begin{theorem}...` | `:::theorem "L" ...` |
| `\begin{proof} \uses{U} \leanok BODY \end{proof}` | `:::proof "L" (uses := "U")` ⏎ `BODY` ⏎ `:::` where `L` = label of the immediately preceding statement |
| `\leanok` | delete (status is computed from Lean) |
| commented-out macros (`%\uses{}` etc.) and pure comment lines | delete |

Rules:
- **All directive options go on the `:::` opening line** (one long line is fine;
  never wrap). The parity checker depends on this.
- Keep every label **verbatim** (`def:WittAlgebra`, `lem:...`, `thm:...` — colons
  and dots are supported).
- Keep `uses` lists and `lean` lists verbatim (same names, same order; separate
  with `, `). Collapse multi-line `\lean{...}` arguments to one line.
- A statement's bracket title `[T]` becomes a bold run-in `*T.*` as the first
  body line (there is no title option in verso-blueprint). If the environment has
  no `[T]`, no run-in title.
- Proof directives take **only** the `uses` option (never `lean`; `priority` etc.
  are statement-only).

## Prose mapping

| LaTeX | Verso |
|---|---|
| `Definition~\ref{def:X}` / `Lemma~\ref{lem:X}` / `Theorem~\ref{thm:X}` | `{bpref "def:X"}[]` (the word Definition/Lemma/… is generated — drop it from the prose) |
| `Definitions~\ref{def:X} and~\ref{def:Y}` | `{bpref "def:X"}[] and {bpref "def:Y"}[]` |
| `(\ref{eq:...})` references to equations | none exist in the chapters; if you find one, keep the sentence meaningful and note the deviation |
| `\term{X}` | `*X*` (Verso bold is single `*`) |
| `\emph{X}` / `\textbf{X}` | `_X_` / `*X*` (Verso: `_..._` = emphasis, `*...*` = bold) |
| `` \verb|X| `` or `\texttt{X}` | `` `X` `` |
| `\item` lists | markdown `-` or `1.` lists |
| `~` (non-breaking space) | plain space |
| `\%`, `\&` etc. | literal character |

## Math mapping

| LaTeX | Verso |
|---|---|
| `$X$` | ``$`X` `` |
| `\begin{align*} X \end{align*}` | `` $$`\begin{aligned} X \end{aligned}` `` (block, blank line before and after) |
| `\begin{align} \label{eq:L} X \end{align}` | same as `align*`: use `aligned`, **drop the `\label`** (no equation refs exist). Numbering is lost — acceptable, documented. |
| `\begin{cases}` | keep as-is inside math (KaTeX supports it) |

- Math macros (`\bbk`, `\witt`, `\vir`, `\hei`, `\Loper`, `\Joper`, `\Verma`,
  `\FockSpace`, `\normalOrder{...}`, `\Coc`, `\Coh`, …) are defined in
  `TeXPrelude.lean` — keep using them **unchanged** inside math.
- Keep alignment ampersands `&` and `\\` line breaks exactly as in the source.
- KaTeX renders the math; if something exotic fails it degrades gracefully —
  do not rewrite formulas to placate the renderer; note it instead.

## What NOT to do

- No `autoDeps`, `uses_intent`, `uses_origin`, `owner`, `priority`, `effort`.
- No invented `uses` edges (even "obviously missing" ones), no dropped edges.
- No `tex` witness blocks (parity is machine-checked against the LaTeX sources).
- No reflowing of paragraph text beyond what the syntax requires; keep the
  source's line breaks where practical (diff-friendliness).

## Worked example

See `VirasoroBlueprint/Chapters/VirasoroAlgebra.lean` (port of
`blueprint/src/chapters/virasoro_algebra.tex`) for the canonical style.

## Validation

From `blueprint-verso/`: `python3 scripts/parity_check.py` — your chapter's
nodes must show no MISMATCH lines (edges into not-yet-ported chapters appear as
"undefined label" until the other chapters land; ignore only those).
