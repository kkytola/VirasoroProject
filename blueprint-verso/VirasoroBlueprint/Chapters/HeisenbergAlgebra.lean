import Verso
import VersoManual
import VersoBlueprint
import VirasoroProject.HeisenbergAlgebra
import VirasoroBlueprint.TeXPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Heisenberg algebra" =>

In this section we assume that $`\bbk` is a field of characteristic zero.

:::definition "def:HeisenbergCocycle" (uses := "def:LieTwoCocycle") (lean := "VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycle")
*Heisenberg cocycle.*
Let $`\gLie` be the vector space with basis $`(j_k)_{k \in \bZ}` over $`\bbk`,
considered as an abelian Lie algebra.
The bilinear map $`{\gamma}_{\hei} \colon \gLie \times \gLie \to \bbk`
given on basis elements by

$$`\begin{aligned}
    {\gamma}_{\hei}(j_k, j_l) = k \, \delta_{k+l,0}
\end{aligned}`

is a Lie algebra 2-cocycle, $`{\gamma}_{\hei} \in C^2(\gLie,\bbk)`.
We call $`{\gamma}_{\hei}` the *Heisenberg cocycle*.
:::

:::lemma_ "lem:HeisenbergCocycleNontrivial" (uses := "def:HeisenbergCocycle, def:LieTwoCohomology") (lean := "VirasoroProject.AbelianLieAlgebraOn.heisenbergCocycle_ne_zero")
*The Heisenberg cocyle is nontrivial.*
The cohomology class $`[{\gamma}_{\hei}] \in H^2(\gLie,\bbk)`
of the Heisenberg cocycle is nonzero.
:::

:::proof "lem:HeisenbergCocycleNontrivial"
…
:::

:::definition "def:HeisenbergAlgebra" (uses := "def:HeisenbergCocycle, def:CentralExtensionOfCocycle") (lean := "VirasoroProject.HeisenbergAlgebra, VirasoroProject.HeisenbergAlgebra.instLieAlgebra, VirasoroProject.HeisenbergAlgebra.isCentralExtension")
*Heisenberg algebra.*
Let $`\bbk` be a field of characteristic zero.
The *Heisenberg algebra* $`\hei` is the Lie algebra over $`\bbk`
obtained as the central extension of the abelian Lie algebra $`\gLie`
with basis $`(j_k)_{k \in \bZ}`,
corresponding to the Heisenberg cocycle $`{\gamma}_{\hei} \in C^2(\gLie,\bbk)`.
:::

From the definition of the Heisenberg algebra and the Heisenberg cocycle,
{bpref "def:HeisenbergAlgebra"}[] and {bpref "def:HeisenbergCocycle"}[],
we directly obtain that $`\hei` has a basis of the following form.

:::definition "def:HeisenbergBasis" (uses := "def:HeisenbergAlgebra") (lean := "VirasoroProject.HeisenbergAlgebra.basisJK")
*The standard basis of the Heisenberg algebra.*
The Heisenberg algebra $`\hei` has a basis consisting of $`(J_k)_{k \in \bZ}`
and $`K`, with Lie brackets determined by the following

$$`\begin{aligned}
    [J_k, J_l] = k \, \delta_{k+l,0} \, K , \quad
    [K, J_k] = 0 , \quad
    [K, K] = 0 ,
\end{aligned}`

for $`k,l \in \bZ`.
:::
