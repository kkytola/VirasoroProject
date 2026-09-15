import Verso
import VersoManual
import VersoBlueprint
import VirasoroProject.CyclicTripleSum
import VirasoroProject.LieCohomologySmallDegree
import VirasoroBlueprint.TeXPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Lie algebra cohomology in degree two" =>

Let $`\bbk` be a field and let $`\gLie` be a Lie algebra over $`\bbk`.
Fix also a vector space $`\aLie` over $`\bbk`, (interpreted, when necessary,
as an abelian Lie algebra, i.e., all Lie brackets in $`\aLie` are taken to
be zero).

:::definition "def:CyclicTripleSum" (lean := "VirasoroProject.cyclicTripleSum, VirasoroProject.cyclicTripleSumHom")
*Cyclic triple sum.*
TO BE WRITTEN
:::

:::definition "def:LieOneCochain" (lean := "VirasoroProject.LieOneCochain")
*Lie algebra 1-cochain.*
A *1-cochain* of the Lie algebra $`\gLie` with coefficients in the vector
space $`\aLie` is a linear map

$$`\begin{aligned}
    \beta \colon \gLie \to \aLie .
\end{aligned}`

The set of all such 1-cochains is denoted by $`\Coch^1(\gLie, \aLie)`.
:::

:::definition "def:LieTwoCocycle" (lean := "VirasoroProject.LieTwoCocycle")
*Lie algebra 2-cocycle.*
A *2-cocycle* of the Lie algebra $`\gLie` with coefficients in the vector
space $`\aLie` is a bilinear map

$$`\begin{aligned}
    \gamma \colon \gLie \times \gLie \to \aLie
\end{aligned}`

such that for all $`X \in \gLie` we have the antisymmetry condition

$$`\begin{aligned}
    \gamma(X,X) = \; & 0
\end{aligned}`

and for all $`X,Y,Z \in \gLie` we have the Leibnitz rule

$$`\begin{aligned}
    \gamma(X,[Y,Z]) = \; & \gamma([X,Y],Z) + \gamma(Y,[X,Z]) .
\end{aligned}`

The set of all such 2-cocycles is denoted by $`\Coc^2(\gLie, \aLie)`.
:::

:::lemma_ "lem:LieTwoCocycle_skew_symmetry" (uses := "def:LieTwoCocycle") (lean := "VirasoroProject.LieTwoCocycle.skew")
*Skew-symmetry of 2-cocycles.*
For any $`\gamma \in \Coc^2(\gLie,\aLie)` and any $`X,Y \in \gLie`,
we have the skew-symmetry property

$$`\begin{aligned}
    \gamma(X,Y) = - \gamma(Y,X) .
\end{aligned}`
:::

:::proof "lem:LieTwoCocycle_skew_symmetry"
The Leibnitz rule
applied to $`X+Y` gives

$$`\begin{aligned}
    0 = \; & \gamma(X+Y,X+Y) \\
      = \; & \gamma(X,X) + \gamma(X,Y) + \gamma(Y,X) + \gamma(Y,Y)
\end{aligned}`

by bilinearity of $`\gamma`. The first and the last terms
in the last expression vanish by antisymmetry,
and the asserted skew-symmetry equation follows.
:::

:::lemma_ "lem:LieOneCochain_vectorSpace" (uses := "def:LieOneCochain") (lean := "VirasoroProject.LieOneCochain.instModule")
*Lie algebra 1-cochains form a vector space.*
The set $`\Coch^1(\gLie, \aLie)` of 1-cochains of $`\gLie` with
coefficients in $`\aLie` forms a vector space over $`\bbk`.
:::

:::proof "lem:LieOneCochain_vectorSpace"
By definition, $`\Coch^1(\gLie, \aLie)` is the space of
linear maps $`\gLie \to \aLie`, and such linear maps form
a vector space.
:::

:::lemma_ "lem:LieTwoCocycle_vectorSpace" (uses := "def:LieTwoCocycle") (lean := "VirasoroProject.LieTwoCocycle.instModule")
*Lie algebra 2-cocycles form a vector space.*
The set $`\Coc^2(\gLie, \aLie)` of 2-cocycles of $`\gLie` with
coefficients in $`\aLie` forms a vector space over $`\bbk`.
:::

:::proof "lem:LieTwoCocycle_vectorSpace"
The conditions defining $`\Coc^2(\gLie, \aLie)` are linear,
so this is staightforward.
:::

:::definition "def:LieTwoCoboundary" (uses := "lem:LieTwoCocycle_vectorSpace, lem:LieOneCochain_vectorSpace") (lean := "VirasoroProject.LieOneCochain_bdryHom")
*Lie algebra 2-coboundary.*
Given a 1-cochain $`\beta \in \Coch^1(\gLie, \aLie)`, we define the
*coboundary* $`\partial \beta` of $`\beta` to be the bilinear map

$$`\begin{aligned}
    \partial \beta \colon \; & \gLie \times \gLie \to \aLie \\
\end{aligned}`

given by

$$`\begin{aligned}
    \partial \beta (X, Y) = \; & \beta ([X,Y]) .
\end{aligned}`

We then have $`\partial \beta \in \Coc^2(\gLie,\aLie)`.
The mapping $`\partial \colon \Coch^1(\gLie,\aLie) \to \Coc^2(\gLie,\aLie)`
is linear. Its range is denoted $`\Cob^2(\gLie,\aLie) \subset \Coc^2(\gLie,\aLie)`
and called the set of *2-coboundaries* of the Lie algebra $`\gLie`
with coefficients in $`\aLie`.
:::

:::definition "def:LieTwoCohomology" (uses := "def:LieTwoCoboundary") (lean := "VirasoroProject.LieTwoCohomology")
*Lie algebra 2-cohomology.*
The vector space

$$`\begin{aligned}
    \Coh^2(\gLie,\aLie) := \Coc^2(\gLie,\aLie) \, / \, \Cob^2(\gLie,\aLie)
\end{aligned}`

is called the *Lie algebra cohomology in degree 2* of $`\gLie`
with coefficients in $`\aLie`.
:::

:::lemma_ "lem:LieTwoCohomology_abelian" (uses := "def:LieTwoCohomology") (lean := "VirasoroProject.LieTwoCocycle.toLieTwoCohomologyEquiv_toLinearMap")
*Cohomology of abelian Lie algebras.*
If $`\gLie` is abelian, i.e., $`[\gLie,\gLie] = 0`, then
the canonical projection

$$`\begin{aligned}
    \Coc^2(\gLie,\aLie) \to \Coh^2(\gLie,\aLie)
\end{aligned}`

is a linear isomorphism.
:::

:::proof "lem:LieTwoCohomology_abelian"
The projection is surjective by construction, so it suffices to show that it is also injective.
The kernel of the projection is $`\Cob^2(\gLie,\aLie) = \Ima \; \partial`.
In view of {bpref "def:LieTwoCoboundary"}[],
abelianity of $`\gLie` implies $`\partial \beta = 0` for any $`\beta \in \Coch^1(\gLie,\aLie)`.
Therefore $`\Cob^2(\gLie,\aLie) = 0`, and the kernel of the projection is trivial,
so the projection is indeed injective.
:::
