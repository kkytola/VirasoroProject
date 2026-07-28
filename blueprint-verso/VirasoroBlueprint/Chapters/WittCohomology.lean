import Verso
import VersoManual
import VersoBlueprint
import VirasoroProject.WittAlgebra
import VirasoroProject.VirasoroCocycle
import VirasoroProject.WittAlgebraCohomology
import VirasoroBlueprint.TeXPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Witt algebra and its 2-cohomology" =>

# Definition of the Witt algebra

:::definition "def:WittAlgebra" (lean := "VirasoroProject.WittAlgebra, VirasoroProject.WittAlgebra.bracket")
*Witt algebra.*
Let $`\bbk` be a field (or a commutative ring). The *Witt algebra* over $`\bbk` is
the $`\bbk`-vector space $`\witt` (or free $`\bbk`-module) with basis $`(\ell_n)_{n \in \bZ}`
and a $`\bbk`-bilinear bracket $`\witt \times \witt \to \witt` given on basis
elements by

$$`\begin{aligned}
    [\ell_n , \ell_m] = (n-m) \, \ell_{n+m} .
\end{aligned}`
:::

With some assumptions on $`\bbk`, the Witt algebra $`\witt` with the above
bracket is an $`\infty`-dimensional Lie algebra over $`\bbk`.

:::lemma_ "lem:WittAlgebraIsLieAlgebra" (uses := "def:WittAlgebra") (lean := "VirasoroProject.WittAlgebra.instLieAlgebra")
*Witt algebra is a Lie algebra.*
If $`\bbk` is a field of characteristic zero, then $`\witt` is
a Lie algebra over $`\bbk`.

(In the case when $`\bbk` is a commutative ring, the $`\witt` is also
a Lie algebra assuming the $`\bbk` has characteristic zero and
that for $`c \in \bbk` and $`X \in \witt` we have $`c \cdot X = 0` only if
either $`c = 0` or $`X = 0`.)
:::

:::proof "lem:WittAlgebraIsLieAlgebra" (uses := "def:CyclicTripleSum")
By construction, the bracket in {bpref "def:WittAlgebra"}[] is
bilinear. It is antisymmetric on the basis vectors $`\ell_n`, $`n \in \bZ`,
so by bilinearity the bracket is antisymmetric.
It remains to check that the bracket satisfies Leibnitz rule
(or the Jacobi identity), i.e., that for any $`X, Y, X \in \witt` we have

$$`\begin{aligned}
    \big[X, [Y, Z] \big] = \big[[X, Y] , Z \big] + \big[Y , [X, Z] \big] .
\end{aligned}`

This formula is trilinear in $`X,Y,Z`, so it suffices to verify it on
basis vectors $`X = \ell_n`, $`Y = \ell_m`, $`Z = \ell_k`.
Calculating, with {bpref "def:WittAlgebra"}[], we have

$$`\begin{aligned}
      \big[\ell_n, [\ell_m, \ell_k] \big]
    = \big[\ell_n, (m-k) \ell_{m+k} \big]
    = (m-k) \big(n-(m+k)\big) \, \ell_{n+m+k}
\end{aligned}`

and

$$`\begin{aligned}
         & \big[[\ell_n, \ell_m] , \ell_k \big] + \big[\ell_m , [\ell_n, \ell_k] \big] \\
    = \; & \big[(n-m) \ell_{n+m} , \ell_k \big] + \big[\ell_m , (n-k) \ell_{n+k}] \big] \\
    = \; & (n-m) \big( n+m-k \big) \, \ell_{n+m+k}  + (n-k) \big( m-(n+k) \big) \, \ell_{m+n+k} .
\end{aligned}`

Noting that

$$`\begin{aligned}
    (n-m) \big( n+m-k \big) + (n-k) \big( m-(n+k) \big)
    = (m-k) \big(n-(m+k)\big) ,
\end{aligned}`

the Leibniz rule follows.
:::

# Virasoro cocycle

In this section we assume that $`\bbk` is a field of characteristic zero
and $`\witt` is the Witt algebra over $`\bbk` as in
{bpref "def:WittAlgebra"}[].

:::definition "def:VirasoroCocycle" (uses := "lem:WittAlgebraIsLieAlgebra, def:LieTwoCocycle") (lean := "VirasoroProject.WittAlgebra.virasoroCocycle")
*Virasoro cocycle.*
The bilinear map $`{\gamma}_{\vir} \colon \witt \times \witt \to \bbk`
given on basis elements of $`\witt` by

$$`\begin{aligned}
    {\gamma}_{\vir}(\ell_n,\ell_m) = \frac{n^3 - n}{12} \, \delta_{n+m,0}
\end{aligned}`

is
called the *Virasoro cocycle*.
:::

:::lemma_ "lem:VirasoroCocycle_is_TwoCocycle" (uses := "def:VirasoroCocycle") (lean := "VirasoroProject.WittAlgebra.virasoroCocycle")
*The Virasoro cocycle is a 2-cocycle.*
The Virasoro cocycle is a 2-cocycle, $`{\gamma}_{\vir} \in \Coc^2(\witt,\bbk)`.
:::

:::proof "lem:VirasoroCocycle_is_TwoCocycle"
By the construction if {bpref "def:VirasoroCocycle"}[],
$`{\gamma}_{\vir} \colon \witt \times \witt \to \bbk` is bilinear.
It's antisymmetry on basis elements of the Witt algebra is easily checked,
so $`{\gamma}_{\vir}` is antisymmetric. It remains to prove the Leibniz
rule for $`{\gamma}_{\vir}`, i.e., that for $`X,Y,X \in \witt`, we have

$$`\begin{aligned}
    {\gamma}_{\vir}(X,[Y,Z]) = \; & {\gamma}_{\vir}([X,Y],Z) + {\gamma}_{\vir}(Y,[X,Z]) .
\end{aligned}`

This formula is trilinear in $`X,Y,Z`, so it suffices to verify it for basis
vectors $`X=\ell_n`, $`Y=\ell_m`, $`Z=\ell_k`. We calculate

$$`\begin{aligned}
    {\gamma}_{\vir}(\ell_n , [\ell_m , \ell_k])
    = \; & {\gamma}_{\vir}\big( \ell_n , (m-k) \ell_{m+k} \big) \\
    = \; & (m-k) \, \frac{n^3 - n}{12} \delta_{n+m+k,0} .
\end{aligned}`

and

$$`\begin{aligned}
         & {\gamma}_{\vir}([\ell_n , \ell_m] , \ell_k)
          + {\gamma}_{\vir}(\ell_m , [\ell_n , \ell_k]) \\
    = \; & {\gamma}_{\vir}((n-m) \ell_{n+m} , \ell_k)
          + {\gamma}_{\vir}(\ell_m , (n-k) \ell_{n+k}) \\
    = \; & (n-m) \, \frac{(n+m)^3 - (n+m)}{12} \delta_{n+m+k,0}
          + (n-k) \, \frac{m^3-m}{12} \delta_{n+m+k,0} .
\end{aligned}`

Both of the above results are nonzero only if $`k=-(n+m)`,
in which case $`m-k = 2m+n` and $`n-k = 2n+m`,
so it suffices to note that

$$`\begin{aligned}
    (2m+n) \, (n^3 - n)
      = (n-m) \, \big( (n+m)^3 - (n+m) \big)
        + (2 n + m) (m^3 - m)
\end{aligned}`

to verify the Leibniz rule for $`{\gamma}_{\vir}`.
:::

:::lemma_ "lem:VirasoroCocycleNontrivial" (uses := "lem:VirasoroCocycle_is_TwoCocycle, def:LieTwoCohomology") (lean := "VirasoroProject.WittAlgebra.cohomologyClass_virasoroCocycle_ne_zero")
*The Virasoro cocyle is nontrivial.*
The cohomology class $`[{\gamma}_{\vir}] \in \Coh^2(\witt,\bbk)`
of the Virasoro cocycle is nonzero.
:::

:::proof "lem:VirasoroCocycleNontrivial"
Assume, by way of contradiction, that $`{\gamma}_{\vir} \in \Cob^2(\witt,\bbk)`,
i.e., that $`{\gamma}_{\vir} = \partial \beta` for some $`\beta \in \Coch^1(\witt,\bbk)`.
Then, in particular, for every $`n \in \bZ` we would have

$$`\begin{aligned}
    {\gamma}_{\vir}(\ell_n,\ell_{-n})
      = \beta \big( [\ell_n, \ell_{-n}] \big) = 2 n \, \beta ( \ell_0 ) .
\end{aligned}`

By {bpref "def:VirasoroCocycle"}[], this would imply

$$`\begin{aligned}
    \frac{n^3-n}{12} = 2 n \, \beta ( \ell_0 )
\end{aligned}`

for all $`n \in \bZ`. Considering for example $`n=3` and $`n=6`, we then get

$$`\begin{aligned}
    2 = 6 \, \beta (\ell_0)
    \qquad \text{ and } \qquad
    \frac{35}{2} = 12 \,  \beta (\ell_0) ,
\end{aligned}`

which obviously yield a contradiction.
:::

# Witt algebra 2-cohomology

:::lemma_ "lem:WittTwoCocycleEquation" (uses := "lem:WittAlgebraIsLieAlgebra, def:LieTwoCocycle") (lean := "VirasoroProject.WittAlgebra.add_lieTwoCocycle_apply_lgen_lgen_lgen_eq_zero")
*Witt algebra 2-cocycle condition for basis.*
For any Witt algebra 2-cocycle $`\gamma \in \Coc^2(\witt,\bbk)` with coefficients
in $`\bbk`, we have

$$`\begin{aligned}
       (m-k) \, \gamma \big( \ell_n , \ell_{m+k} \big)
     + (k-n) \, \gamma \big( \ell_{m} , \ell_{n+k} \big)
     + (n-m) \, \gamma \big( \ell_k , \ell_{n+m} \big)
     \; = \; 0
\end{aligned}`

for all $`n,m,k \in \bZ`.
:::

:::proof "lem:WittTwoCocycleEquation"
Direct calculation, using {bpref "def:WittAlgebra"}[]
and {bpref "def:LieTwoCocycle"}[].
:::

:::lemma_ "lem:WittTwoCocycleSupport" (uses := "lem:WittAlgebraIsLieAlgebra, def:LieTwoCocycle") (lean := "VirasoroProject.WittAlgebra.lieTwoCocycle_apply_lgen_lgen_eq_zero_of_add_ne_zero")
*Witt algebra 2-cocycle support assuming normalization.*
Let $`\gamma \in \Coc^2(\witt,\bbk)` be a Witt algebra 2-cocycle such that
$`\gamma (\ell_0 , \ell_n) = 0` for all $`n \in \bZ`.
Then for any $`n,m \in \bZ` with $`n+m \ne 0`, we have

$$`\begin{aligned}
    \gamma(\ell_n , \ell_m) = 0.
\end{aligned}`
:::

:::proof "lem:WittTwoCocycleSupport" (uses := "lem:WittTwoCocycleEquation, lem:LieTwoCocycle_skew_symmetry")
Apply {bpref "lem:WittTwoCocycleEquation"}[] with $`k=0`. The last term
vanishes, and by skew-symmetry of $`\gamma`, the first two terms simplify to yield

$$`\begin{aligned}
    (m+n) \, \gamma (\ell_n , \ell_m) = 0 ,
\end{aligned}`

which, assuming $`n+m \ne 0`, yields the asserted equation
$`\gamma (\ell_n , \ell_m) = 0`.
:::

:::lemma_ "lem:WittTwoCocycleNormalization" (uses := "def:VirasoroCocycle, def:LieTwoCoboundary") (lean := "VirasoroProject.WittAlgebra.exists_add_bdry_eq_smul_virasoroCocycle")
*Normalization of Witt algebra 2-cocycles.*
For any 2-cocycle $`\gamma \in \Coc^2(\witt,\bbk)`, there exists
a coboundary $`\partial \beta` with $`\beta \in \Coch^1(\witt,\bbk)`
such that

$$`\begin{aligned}
    \gamma + \partial \beta \; = \; r \cdot {\gamma}_{\vir}
\end{aligned}`

for some scalar $`r \in \bbk`.
:::

:::proof "lem:WittTwoCocycleNormalization" (uses := "lem:WittTwoCocycleSupport, lem:WittTwoCocycleEquation")
Let $`\gamma \in \Coc^2(\witt,\bbk)` be a Witt algebra 2-cocycle.
Define a Witt algebra 1-cochain $`\beta \in \Coch^1(\witt,\bbk)` by linear extension of

$$`\begin{aligned}
    \beta (\ell_n) =
    \begin{cases}
      -\frac{1}{2} \gamma(\ell_1, \ell_{-1}) & \text{ if } n = 0 \\
      \frac{1}{n} \gamma(\ell_0, \ell_n) & \text{ if } n \ne 0 .
    \end{cases}
\end{aligned}`

For any $`n \ne 0`, we calculate

$$`\begin{aligned}
           \big( \gamma + \partial \beta \big) (\ell_0 , \ell_n)
    = \; & \gamma (\ell_0 , \ell_n) + \beta ([\ell_0,\ell_n]) \\
    = \; & \gamma (\ell_0 , \ell_n) - n \, \beta (\ell_n) \\
    = \; & \gamma (\ell_0 , \ell_n) - n \, \frac{1}{n}\gamma(\ell_0, \ell_n) = 0 .
\end{aligned}`

This property and {bpref "lem:WittTwoCocycleSupport"}[] imply that

$$`\begin{aligned}
    \big( \gamma + \partial \beta \big) (\ell_0 , \ell_n) = 0
\end{aligned}`

whenever $`n+m \ne 0`.

We will show the asserted equation with

$$`\begin{aligned}
    r = 2 \, \big( \gamma + \partial \beta \big) ( \ell_2, \ell_{-2}) .
\end{aligned}`

By comparison with the Virasoro cocycle $`{\gamma}_{\vir}`
of {bpref "def:VirasoroCocycle"}[], and using skew-symmetry,
it remains to show that for any $`n \in \bN` we have

$$`\begin{aligned}
    \big( \gamma + \partial \beta \big) (\ell_n , \ell_{-n})
      = r \; \frac{n^3 - n}{12} .
\end{aligned}`

The case $`n = 0` is a direct consequence of antisymmetry.
The case $`n = 1` follows
using the definition of $`\beta` and the calculation

$$`\begin{aligned}
    \big( \gamma + \partial \beta \big) (\ell_1 , \ell_{-1})
    = \; & \gamma (\ell_1 , \ell_{-1}) + \beta ([\ell_1,\ell_{-1}]) \\
    = \; & \gamma (\ell_1 , \ell_{-1}) + 2 \, \beta (\ell_0) \\
    = \; & \gamma (\ell_1 , \ell_{-1}) - 2 \, \frac{1}{2} \gamma(\ell_1, \ell_{-1}) = 0 .
\end{aligned}`

The case $`n = 2` follows directly by the choice of $`r`.
We prove the equality in the cases $`n \ge 3` by induction on $`n`.
Assume the equation for smaller values of $`n`.
Apply {bpref "lem:WittTwoCocycleEquation"}[] to $`\gamma + \partial \beta`
with $`m = 1-n` and $`k = -1` to get

$$`\begin{aligned}
    0 = \; & (2-n) \, \big( \gamma + \partial \beta \big) (\ell_n , \ell_{-n})
           + (-1-n) \, \big( \gamma + \partial \beta \big) (\ell_{1-n} , \ell_{n-1})
           + (2 n - 1) \, \big( \gamma + \partial \beta \big) (\ell_1 , \ell_{-1}) \\
      = \; & (2-n) \, \big( \gamma + \partial \beta \big) (\ell_n , \ell_{-n})
                  - (-1-n) \, r \frac{(n-1)^3 - (n-1)}{12} \\
      = \; & (2-n) \, \big( \gamma + \partial \beta \big) (\ell_n , \ell_{-n})
           + \frac{r}{12} (n+1) n (n-1) (n-2) .
\end{aligned}`

where in the seciond step we used the induction hypothesis. Since $`2-n \ne 0`, this can
be solved for

$$`\begin{aligned}
           \big( \gamma + \partial \beta \big) (\ell_n , \ell_{-n})
    = \; & - \frac{r}{12} \frac{(n+1) n (n-1) (n-2)}{2-n} = r \frac{n^3 - n}{12} ,
\end{aligned}`

completing the induction step.
:::

:::lemma_ "lem:WittTwoCohomologyIsOneDimensional" (uses := "def:WittAlgebra, def:LieTwoCohomology, lem:VirasoroCocycle_is_TwoCocycle") (lean := "VirasoroProject.WittAlgebra.rank_lieTwoCohomology_eq_one")
*Witt algebra 2-cohomology is spanned by the Virasoro cocycle.*
The Lie algebra 2-cohomology $`\Coh^2(\witt,\bbk)` of the Witt
algebra $`\witt` with coefficients in $`\bbk` is one-dimensional
and spanned by the class of the Virasoro cocycle $`{\gamma}_{\vir}`,

$$`\begin{aligned}
    \Coh^2(\witt,\bbk) \; = \; \bbk \cdot [{\gamma}_{\vir}] .
\end{aligned}`
:::

:::proof "lem:WittTwoCohomologyIsOneDimensional" (uses := "lem:WittTwoCocycleNormalization, lem:VirasoroCocycleNontrivial")
This follows directly from
{bpref "lem:WittTwoCocycleNormalization"}[]
and {bpref "lem:VirasoroCocycleNontrivial"}[].
:::
