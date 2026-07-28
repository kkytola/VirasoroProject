import Verso
import VersoManual
import VersoBlueprint
import VirasoroProject.VirasoroAlgebra
import VirasoroBlueprint.TeXPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Virasoro algebra" =>

:::definition "def:VirasoroAlgebra" (uses := "def:VirasoroCocycle, def:CentralExtensionOfCocycle") (lean := "VirasoroProject.VirasoroAlgebra, VirasoroProject.VirasoroAlgebra.instLieAlgebra, VirasoroProject.VirasoroAlgebra.isCentralExtension")
*Virasoro algebra.*
Let $`\bbk` be a field of characteristic zero.
The *Virasoro algebra* $`\vir` is the Lie algebra over $`\bbk`
obtained as the central extension of the Witt algebra $`\witt`
corresponding to the Virasoro cocycle $`{\gamma}_{\vir} \in C^2(\witt,\bbk)`.
:::

From the definition of the Virasoro algebra and the Virasoro cocycle,
{bpref "def:VirasoroAlgebra"}[] and {bpref "def:VirasoroCocycle"}[],
we directly obtain that $`\vir` has a basis of the following form.

:::definition "def:VirasoroBasis" (uses := "def:VirasoroAlgebra") (lean := "VirasoroProject.VirasoroAlgebra.basisLC")
*The standard basis of the Virasoro algebra.*
The Virasoro algebra $`\vir` has a basis consisting of $`(L_n)_{n \in \bZ}`
and $`C`, with Lie brackets determined by the following

$$`\begin{aligned}
    [L_n, L_m] = \; & (n-m) \, L_{n+m} + \delta_{n+m,0} \frac{n^3 - n}{12} \, C ,
\end{aligned}`

$$`\begin{aligned}
    [C, L_n] = 0 , \qquad
    [C, C] = 0 ,
\end{aligned}`

for $`n,m \in \bZ`.
:::
