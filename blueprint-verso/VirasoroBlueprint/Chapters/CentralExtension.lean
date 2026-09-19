import Verso
import VersoManual
import VersoBlueprint
import VirasoroProject.IsCentralExtension
import VirasoroBlueprint.TeXPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Central extensions of Lie algebras" =>

# Central extensions of Lie algebras

:::definition "def:LieExtension" (lean := "VirasoroProject.LieAlgebra.IsExtension")
*Lie algebra extension.*
An *extension* $`\egLie` of a Lie algebra $`\gLie` by a Lie algebra $`\aLie` is
a Lie algebra together with a pair of two Lie algebra homomorphisms
$`\iota \colon \aLie \longrightarrow \egLie` and
$`\pi \colon \egLie \longrightarrow \gLie` which form a
short exact sequence

$$`\begin{aligned}
    0 \longrightarrow \aLie
      \overset{\iota}{\longrightarrow} \egLie
      \overset{\pi}{\longrightarrow} \gLie
      \longrightarrow 0 ,
\end{aligned}`

i.e., such that $`\iota` is injective, $`\pi` is surjective,
and $`\Ima (\iota) = \Ker (\pi)`.
:::

:::definition "def:LieCentralExtension" (uses := "def:LieExtension") (lean := "VirasoroProject.LieAlgebra.IsCentralExtension")
*Lie algebra central extension.*
A *central extension* $`\egLie` of a Lie algebra $`\gLie` by an abelian Lie algebra $`\aLie` is
a Lie algebra extension

$$`\begin{aligned}
    0 \longrightarrow \aLie
      \overset{\iota}{\longrightarrow} \egLie
      \overset{\pi}{\longrightarrow} \gLie
      \longrightarrow 0
\end{aligned}`

such that $`\Ima (\iota)` is contained in the centre of $`\egLie`,
i.e., $`[\iota(A), W] = 0` for all $`A \in \aLie`, $`W \in \egLie`.
:::

# Central extensions determined by 2-cocycles

:::definition "def:CentralExtensionOfCocycle" (uses := "def:LieCentralExtension, def:LieTwoCocycle") (lean := "VirasoroProject.LieTwoCocycle.CentralExtension, VirasoroProject.LieTwoCocycle.CentralExtension.instLieAlgebra")
*Central extension determined by a cocycle.*
Given a Lie algebra 2-cocycle $`\gamma \in C^2(\gLie,\aLie)`,
on the vector space

$$`\begin{aligned}
    \egLie_\gamma = \gLie \oplus \aLie
\end{aligned}`

define a bracket by

$$`\begin{aligned}
    [(X, A), (Y, B)]_{\gamma} := \big([X, Y]_{\gLie}, \gamma(X, Y) \big) .
\end{aligned}`

Then $`\egLie_\gamma` becomes a Lie algebra with the Lie bracket
$`[\cdot,\cdot]_{\gamma}`.
:::

:::lemma_ "lem:CentralExtensionOfCocycleModCoboundary" (uses := "def:CentralExtensionOfCocycle, def:LieTwoCoboundary") (lean := "VirasoroProject.LieOneCochain_bdryHom, VirasoroProject.LieTwoCocycle.CentralExtension.equiv_of_lieTwoCoboundary")
*Central extension determined by cohomologous cocycles.*
Let $`\gamma_1, \gamma_2 \in C^2(\gLie,\aLie)` be two Lie algebra 2-cocycles
and $`\egLie_{\gamma_1}, \egLie_{\gamma_2}` the central extensions corresponding
to these according to {bpref "def:CentralExtensionOfCocycle"}[].
If the two 2-cocycles differ by a coboundary,
$`\gamma_2 - \gamma_1 = \partial \beta` with some $`\beta \in C^1(\gLie,\aLie)`,
then the mapping $`\egLie_{\gamma_1} \to \egLie_{\gamma_2}` given by

$$`\begin{aligned}
    (X,A) \mapsto \big( X, A + \beta(X) \big)
\end{aligned}`

is an isomophism of Lie algebras $`\egLie_{\gamma_1} \cong \egLie_{\gamma_2}`.
:::

:::proof "lem:CentralExtensionOfCocycleModCoboundary"
The mapping $`\phi_\beta \colon \egLie_1 \to \egLie_2` given by

$$`\begin{aligned}
    \phi_\beta\big((X,A)\big) := \big( X, A + \beta(X) \big)
\end{aligned}`

is clearly linear. It is also bijective, since the similarly defined mapping
$`\phi_{-\beta} \colon \egLie_2 \to \egLie_1`,
$`\phi_{-\beta}\big((X,A)\big) := \big( X, A - \beta(X) \big)`,
is a two-sided inverse to $`\phi_\beta`.
So it remains to verify that this bijective linear map
$`\phi_\beta \colon \egLie_1 \to \egLie_2` is in fact a
homomorphism Lie algebras.

Let $`(X, A), (Y, B) \in \gLie \oplus \aLie = \egLie_{\gamma_1}`.
The bracket in $`\egLie_{\gamma_1}` of these is, by definition,

$$`\begin{aligned}
    [(X, A), (Y, B)]_{\gamma_1} := \big([X, Y]_{\gLie}, \gamma_1(X, Y) \big) .
\end{aligned}`

Applying the mapping $`\phi_\beta` to this, we get

$$`\begin{aligned}
    \phi_\beta \Big([(X, A), (Y, B)]_{\gamma_1} \Big)
      = \big([X, Y]_{\gLie}, \gamma_1(X, Y) + \beta([X, Y]_{\gLie}) \big) .
\end{aligned}`

On the other hand the Lie bracket in $`\egLie_2` of the images is

$$`\begin{aligned}
       & \big[ \phi_\beta\big(((X, A)\big), \phi_\beta\big((Y, B)\big) \big]_{\gamma_2} \\
    = \; & \big[ \big( X, A + \beta(X) \big), \big( Y, B + \beta(Y) \big) \big]_{\gamma_2} \\
    = \; & \Big( [X,Y]_{\gLie} , \gamma_2(X,Y) \Big) \\
    = \; & \Big( [X,Y]_{\gLie} , \gamma_1(X,Y) + \beta([X, Y]_{\gLie}) \Big) .
\end{aligned}`

From the equality of these two expressions we see that $`\phi_\beta`
indeed is also a Lie algebra homomorphism.
:::

:::lemma_ "lem:OfCocycleIsCentralExtension" (uses := "def:CentralExtensionOfCocycle") (lean := "VirasoroProject.LieTwoCocycle.CentralExtension.isCentralExtension")
*Central extension determined by a cocycle is a central extension.*
Given a Lie algebra 2-cocycle $`\gamma \in C^2(\gLie,\aLie)`,
consider the Lie algebra $`\egLie_\gamma = \gLie \oplus \aLie` as
in {bpref "def:CentralExtensionOfCocycle"}[].
With the inclusion $`\iota \colon \aLie \to \gLie \oplus \aLie`
in the second direct summand and the
projection $`\pi \colon \gLie \oplus \aLie \to \gLie` to the first direct
summand, the Lie algebra $`\egLie_\gamma = \gLie \oplus \aLie` becomes a central
extension of $`\gLie` by $`\aLie`, i.e., we have the short exact sequence
of Lie algebras

$$`\begin{aligned}
    0 \longrightarrow \aLie
      \overset{\iota}{\longrightarrow} \egLie_\gamma
      \overset{\pi}{\longrightarrow} \gLie
      \longrightarrow 0 .
\end{aligned}`
:::

:::proof "lem:OfCocycleIsCentralExtension"
Clearly

$$`\begin{aligned}
    0 \longrightarrow \aLie
      \overset{\iota}{\longrightarrow} \egLie_\gamma
      \overset{\pi}{\longrightarrow} \gLie
      \longrightarrow 0
\end{aligned}`

is an exact sequence of vector spaces, and it is straightforward
to check with {bpref "def:CentralExtensionOfCocycle"}[]
that $`\iota` and $`\pi` are Lie algebra homomorphisms.
:::

:::theorem "thm:CentralExtensionOfCohomologyClass" (uses := "def:LieTwoCohomology")
Every cohomology class in $`H^2(\gLie, \aLie)` determines a well-defined
isomorphism class of central extensions of the Lie algebra $`\gLie`
by $`\aLie` by the rule that the class $`[\gamma] \in H^2(\gLie, \aLie)` of
a cocycle $`\gamma \in C^2(\gLie, \aLie)` corresponds to the isomorphism
class of $`\egLie_\gamma` ({bpref "def:CentralExtensionOfCocycle"}[]).
:::

:::proof "thm:CentralExtensionOfCohomologyClass" (uses := "lem:CentralExtensionOfCocycleModCoboundary")
This follows from {bpref "lem:OfCocycleIsCentralExtension"}[]
and {bpref "lem:CentralExtensionOfCocycleModCoboundary"}[].
:::
