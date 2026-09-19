import VersoBlueprint

/-!
Math-mode TeX macros for the Virasoro blueprint, ported from the macro file of the
former plasTeX blueprint (`blueprint/src/macros/common.tex`, removed from the tree
once the Verso blueprint took over; recoverable from the Git history).

Not ported:
- the `\newtheorem` setup (superseded by blueprint node directives);
- `\term` (text-mode; markdown bold is used instead).

Deviation: `\normalOrder` originally expanded to `{\mathbb{:} #1 \mathbb{:}}`;
`\mathbb` applied to a colon is not renderable in KaTeX, so plain colons are
used here (visual change only, the standard physics notation `:A:` remains).
-/

/-
`\mathscr` (used by `\UEA`, `\Verma`, `\FockSpace`) is built into KaTeX but is not
provided by the packages verso-blueprint loads for the PDF (amsmath, amssymb,
mathtools), which made `lake exe vbp build --pdf` fail outright. `\providecommand`
only defines it when it is missing, so the HTML keeps true script glyphs from
KaTeX and only the PDF falls back to calligraphic ones.
-/
tex_prelude r#"
\providecommand{\mathscr}{\mathcal}
"#

tex_prelude r#"
\newcommand{\bN}{\mathbb{N}}
\newcommand{\bZ}{\mathbb{Z}}
\newcommand{\bQ}{\mathbb{Q}}
\newcommand{\bR}{\mathbb{R}}
\newcommand{\bC}{\mathbb{C}}
\newcommand{\bbk}{\mathbb{K}}
"#

tex_prelude r#"
\newcommand{\gLie}{\mathfrak{g}}
\newcommand{\aLie}{\mathfrak{a}}
\newcommand{\egLie}{\mathfrak{h}}
\newcommand{\hei}{\mathfrak{hei}}
\newcommand{\witt}{\mathfrak{witt}}
\newcommand{\vir}{\mathfrak{vir}}
\newcommand{\UEA}{\mathscr{U}}
"#

tex_prelude r#"
\newcommand{\Joper}{\mathsf{J}}
\newcommand{\Loper}{\mathsf{L}}
\newcommand{\tagHeiComm}{\textrm{(HeiComm)}}
\newcommand{\tagHeiTrunc}{\textrm{(HeiTrunc)}}
\newcommand{\normalOrder}[1]{{{:}#1{:}}}
"#

tex_prelude r#"
\newcommand{\Verma}{\mathscr{V}}
\newcommand{\VermaHWV}{\mathbb{v}}
\newcommand{\FockSpace}{\mathscr{F}}
\newcommand{\FockVacuum}{\mathbb{v}}
"#

tex_prelude r#"
\newcommand{\id}{\mathrm{id}}
\newcommand{\idOf}[1]{\id_{{#1}}}
\newcommand{\indicator}[1]{\mathbb{I}_{{#1}}}
\newcommand{\Ima}{\mathrm{Im}}
\newcommand{\Ker}{\mathrm{Ker}}
\newcommand{\Coc}{\mathrm{Z}}
\newcommand{\Coch}{\mathrm{C}}
\newcommand{\Cob}{\mathrm{B}}
\newcommand{\Coh}{\mathrm{H}}
"#
