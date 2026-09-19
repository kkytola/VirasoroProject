import Verso
import VersoManual
import VersoBlueprint
import VirasoroProject.Sugawara
import VirasoroProject.CentralChargeCalc
import VirasoroProject.FockSpace
import VirasoroProject.FockSpaceSugawara
import VirasoroBlueprint.TeXPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Sugawara construction" =>

# The basic bosonic Sugawara construction

Throughout this section, let $`\bbk` be a field of characteristic zero.

If a vector space $`V` has a representation
of the Heisenberg algebra on a vector space $`V`,
where the central element $`K` (see {bpref "def:HeisenbergBasis"}[]),
acts as $`\id_V`, then the basis elements $`(J_k)_{k \in \bZ}`
(see {bpref "def:HeisenbergBasis"}[]) are linear operators $`\Joper_k \colon V \to V`
satisfying the commutation relations

$$`\begin{aligned}
  \mathrm{\tagHeiComm} \qquad
  [\Joper_k, \Joper_l]
  \; = \; \Joper_k \circ \Joper_l - \Joper_l \circ \Joper_k
  \; = \; k \, \delta_{k+l,0} \; \id_V .
\end{aligned}`

Below we will assume such operators being fixed, and satisfying furthermore the
local truncation condition on $`V`: for any fixed $`v \in V` we have
$`\Joper_k \, v = 0` for $`k \gg 0`, i.e.,

$$`\begin{aligned}
  \mathrm{\tagHeiTrunc} \qquad
  \forall v \in V , \; \exists N, \; \forall k \ge N, \quad
  \Joper_k \, v = 0 .
\end{aligned}`

:::definition "def:NormalOrdering" (lean := "VirasoroProject.pairNO")
*Normal ordering.*
For $`k,l \in \bZ`, we denote the normal ordered product of the operators $`\Joper_k`
and $`\Joper_l` by

$$`\begin{aligned}
    \normalOrder{\Joper_k \, \Joper_l} \; := \;
    \begin{cases}
      \Joper_k \circ \Joper_l & \text{ if } k \le l \\
      \Joper_l \circ \Joper_k & \text{ if } k \, > \, l .
    \end{cases}
\end{aligned}`
:::

:::lemma_ "lem:AlternativeNormalOrdering" (uses := "def:NormalOrdering") (lean := "VirasoroProject.heiOper_pairNO_eq_pairNO'")
*Alternative normal ordering.*
Suppose that $`(\Joper_{k})_{k \in \bZ}` satisfy the commutation relations
$`\tagHeiComm{}`. Then for any $`k,l \in \bZ` we have

$$`\begin{aligned}
    \normalOrder{\Joper_k \, \Joper_l} \; = \;
    \begin{cases}
      \Joper_k \circ \Joper_l & \text{ if } k < 0 \\
      \Joper_l \circ \Joper_k & \text{ if } k \ge 0 .
    \end{cases}
\end{aligned}`
:::

:::proof "lem:AlternativeNormalOrdering"
Straightforward using the commutation relations $`\tagHeiComm{}`.
:::

:::lemma_ "lem:NormalOrderingTruncation" (uses := "def:NormalOrdering") (lean := "VirasoroProject.pairNO_apply_eq_zero")
*Local truncation for normal ordered products.*
Suppose that $`(\Joper_{k})_{k \in \bZ}` satisfy the local truncation condition
$`\tagHeiTrunc{}`. Then for any $`v \in V` there exists an $`N` such that
whenever $`\max \{k,l\} \ge N` we have
$`\normalOrder{\Joper_{k} \, \Joper_{l}} \, v = 0`.
:::

:::proof "lem:NormalOrderingTruncation"
Fixing $`v \in V`, the local truncation condition $`\tagHeiTrunc{}`
gives the existence of an $`N` such that $`\Joper_{k} \, v = 0`
for $`k \ge N`. It is then clear by inspection of {bpref "def:NormalOrdering"}[]
that $`\normalOrder{\Joper_{k} \, \Joper_{l}} \, v = 0` when
$`\max \{k,l\} \ge N`.
:::

:::lemma_ "lem:NormalOrderingFiniteSupport" (uses := "def:NormalOrdering") (lean := "VirasoroProject.hasFiniteSupport_smul_pairNO_apply")
*Local finite support for homogeneous normal ordered products.*
Suppose that $`(\Joper_{k})_{k \in \bZ}` satisfy the local truncation condition
$`\tagHeiTrunc{}`. Then for any $`n \in \bZ` and any $`v \in V`,
there are only finitely many $`k \in \bZ` such that
$`\normalOrder{\Joper_{n-k} \, \Joper_k} \, v \ne 0`.
:::

:::proof "lem:NormalOrderingFiniteSupport" (uses := "lem:NormalOrderingTruncation")
Straightforward from {bpref "lem:NormalOrderingTruncation"}[].
:::

:::definition "def:SugawaraOperator" (uses := "def:NormalOrdering, lem:NormalOrderingFiniteSupport") (lean := "VirasoroProject.sugawaraGen")
*Sugawara operators.*
Suppose that $`(\Joper_{k})_{k \in \bZ}` satisfy the local truncation condition
$`\tagHeiTrunc{}`. Then for any $`n \in \bZ`, a linear operator

$$`\begin{aligned}
    \Loper_n \colon V \to V
\end{aligned}`

can be defined by the formula

$$`\begin{aligned}
    \Loper_n \, v := \frac{1}{2} \sum_{k \in \bZ} \normalOrder{\Joper_{n-k} \, \Joper_k} \, v
    \qquad \text{ for } v \in V
\end{aligned}`

(the sum only has finitely many terms by {bpref "lem:NormalOrderingFiniteSupport"}[]).

We call the operators $`(\Loper_n)_{n \in \bZ}` the *Sugawara operators*.
:::

:::lemma_ "lem:SugawaraCommutatorSeries" (uses := "def:SugawaraOperator") (lean := "VirasoroProject.commutator_sugawaraGen_apply_eq_finsum_commutator_apply")
*Commutators of Sugawara operators as series.*
Suppose that $`(\Joper_{k})_{k \in \bZ}` satisfy the local truncation condition
$`\tagHeiTrunc{}`, and suppose that $`\mathsf{A} \colon V \to V` is a linear operator.
Then for any $`n \in \bZ`, the action of the commutator $`[\Loper_n, \mathsf{A}]`
on any $`v \in V` is given by the series

$$`\begin{aligned}
    [\Loper_n, \mathsf{A}] \, v =
    \frac{1}{2} \sum_{k \in \bZ} [\normalOrder{\Joper_{n-k} \, \Joper_k}, \mathsf{A}] \, v
\end{aligned}`

where only finitely many of the terms are nonzero.
:::

:::proof "lem:SugawaraCommutatorSeries" (uses := "lem:NormalOrderingFiniteSupport")
Write

$$`\begin{aligned}
    [\Loper_n, A] \, v
    = \; & \Loper_n \, A \, v - A \, \Loper_n \, v \\
    = \; & \frac{1}{2} \sum_{k \in \bZ} \normalOrder{\Joper_{n-k} \, \Joper_k} \, \mathsf{A} \, v
        - \frac{1}{2} \mathsf{A} \sum_{k \in \bZ} \normalOrder{\Joper_{n-k} \, \Joper_k} \, v .
\end{aligned}`

By {bpref "lem:NormalOrderingFiniteSupport"}[], only finitely many of the terms
in both sums are nonzero and they may be rearranged to the asserted form of sum of
commutators. The resulting sum only has finitely many nonzero terms and is therefore
well-defined.
:::

:::lemma_ "lem:CommutatorSugawaraHeisenberg" (uses := "def:SugawaraOperator") (lean := "VirasoroProject.commutator_sugawaraGen_heiOper")
*Commutator of Sugawara operators with Heisenberg operators.*
Suppose that $`(\Joper_{k})_{k \in \bZ}` satisfy the commutation relations
$`\tagHeiComm{}` and the local truncation condition
$`\tagHeiTrunc{}`. Then for any $`n \in \bZ` and $`k \in \bZ`, we have

$$`\begin{aligned}
    [\Loper_n, \Joper_k] \; = \;
    - k \, \Joper_{n+k} .
\end{aligned}`
:::

:::proof "lem:CommutatorSugawaraHeisenberg" (uses := "lem:SugawaraCommutatorSeries")
Calculation, using {bpref "lem:SugawaraCommutatorSeries"}[] and
the commutator formula $`[A,BC] = B[A,C] + [A,B]C`.
:::

:::lemma_ "lem:CommutatorSugawaraNormalOrderedPair" (uses := "def:SugawaraOperator") (lean := "VirasoroProject.commutator_sugawaraGen_heiPairNO'")
*Commutator of Sugawara operators with normal ordered pairs.*
Suppose that $`(\Joper_{k})_{k \in \bZ}` satisfy the commutation relations
$`\tagHeiComm{}` and the local truncation condition
$`\tagHeiTrunc{}`. Then for any $`n \in \bZ` and $`k, m \in \bZ`, we have

$$`\begin{aligned}
    [\Loper_n, \normalOrder{\Joper_k \, \Joper_{m-k}}]
    = \; &
    -k \, \normalOrder{\Joper_{n+k} \, \Joper_{m-k}}
    - (m-k) \, \normalOrder{\Joper_{k} \, \Joper_{n+m-k}} \\
      & \; + k \, (n+k) \, \delta_{n+m,0}
        \Big( \indicator{k + n \le 0} - \indicator{k \le 0} \Big) \, \id_V .
\end{aligned}`

where $`\indicator{\mathrm{condition}}` is defined as $`1` if the condition is true
and $`0` otherwise.
:::

:::proof "lem:CommutatorSugawaraNormalOrderedPair" (uses := "lem:CommutatorSugawaraHeisenberg, lem:AlternativeNormalOrdering")
Calculation: by the alternative normal ordering
({bpref "lem:AlternativeNormalOrdering"}[]) and the commutation relations $`\tagHeiComm{}`,
the normal ordered product differs from the plain product
$`\Joper_k \, \Joper_{m-k}` by an explicit multiple of $`\id_V`, which is central.
The commutator with the plain product is evaluated using
{bpref "lem:CommutatorSugawaraHeisenberg"}[]
and the commutator formula $`[A,BC] = B[A,C] + [A,B]C`; converting the plain products back
to normal ordered products (again up to explicit multiples of $`\id_V`)
yields the asserted boundary terms.
:::

:::lemma_ "lem:AuxiliaryCentralChargeCalculation" (lean := "VirasoroProject.bosonic_sugawara_cc_calc_nonneg")
*Auxiliary calculation.*
For any $`n \in \bN`, we have

$$`\begin{aligned}
    \sum_{l=0}^{n-1} (n-l) l = \frac{n^3 - n}{6} .
\end{aligned}`
:::

:::proof "lem:AuxiliaryCentralChargeCalculation"
Calculation (with induction).
:::

:::lemma_ "lem:CommutatorSugawara" (uses := "def:SugawaraOperator") (lean := "VirasoroProject.commutator_sugawaraGen")
*Virasoro commutation relations for Sugawara operators.*
Suppose that $`(\Joper_{k})_{k \in \bZ}` satisfy the commutation relations
$`\tagHeiComm{}` and the local truncation condition
$`\tagHeiTrunc{}`. Then for any $`n, m \in \bZ`, we have

$$`\begin{aligned}
    [\Loper_n, \Loper_m]
    = \; &
    (n-m) \, \Loper_{n+m} + \delta_{n+m,0} \frac{n^3 - n}{12} \, \id_V .
\end{aligned}`
:::

:::proof "lem:CommutatorSugawara" (uses := "lem:CommutatorSugawaraNormalOrderedPair, lem:AuxiliaryCentralChargeCalculation")
Calculation, using {bpref "lem:CommutatorSugawaraNormalOrderedPair"}[]
and {bpref "lem:AuxiliaryCentralChargeCalculation"}[], among other observations.
:::

:::theorem "thm:SugawaraRepresentation" (uses := "def:SugawaraOperator, def:VirasoroBasis") (lean := "VirasoroProject.sugawaraRepresentation")
*Sugawara construction.*
Suppose that $`(\Joper_{k})_{k \in \bZ}` satisfy the commutation relations
$`\tagHeiComm{}` and the local truncation condition
$`\tagHeiTrunc{}`. Then there exists a representation of the Virasoro algebra $`\vir`
with central charge $`c = 1` on $`V` (i.e.,
the central element $`C \in \vir` acts as $`c \, \id_V` with $`c = 1`)
where the basis elements $`L_n` of $`\vir` act by
the Sugawara operators $`(\Loper_n)_{n \in \bZ}`.
:::

:::proof "thm:SugawaraRepresentation" (uses := "lem:CommutatorSugawara")
A direct consequence of the commutation relations in {bpref "lem:CommutatorSugawara"}[]
and a comparison with the Lie brackets in the basis of {bpref "def:VirasoroBasis"}[].
:::

# Charged Fock spaces (Heisenberg Verma modules)

:::definition "def:HeisenbergTriangular" (uses := "def:TriangularDecomposition, def:HeisenbergBasis") (lean := "VirasoroProject.heisenbergTri")
*Triangular decomposition of the Heisenberg algebra.*
A triangular decomposition

$$`\begin{aligned}
    \hei = \hei^0 \oplus \hei^+ \oplus \hei^-
\end{aligned}`

of $`\hei` is defined so that $`\hei^0` is spanned by $`J_0, K \in \hei`,
$`\hei^+` is spanned by $`J_k` for $`k > 0`,
and $`\hei^-` is spanned by $`J_k` for $`k < 0`.

(Without further comment, for the Heisenberg algebra we always use this
triangular decomposition.)
:::

:::definition "def:ChargedFockSpace" (uses := "def:HeisenbergTriangular, def:LieVermaModule") (lean := "VirasoroProject.ChargedFockSpace")
*Charged Fock space (Heisenberg Verma module).*
Let $`\alpha \in \bbk`.
The *charged Fock space* of charge $`\alpha`
is the Verma module $`\Verma^{\eta}` associated to the linear functional
$`\eta \colon \hei^0 \to \bbk` with

$$`\begin{aligned}
    \eta(J_0) = \alpha, \quad \eta(K) = 1 .
\end{aligned}`

We denote the charged Fock space by $`\FockSpace^{\alpha}`.
The highest weight vector $`\VermaHWV^{\eta}`
is (also) called the *vacuum vector* of the charged Fock space,
and we denote it by $`\FockVacuum^{\alpha}`.
:::

:::lemma_ "lem:HeisenbergEventuallyCommute" (uses := "def:HeisenbergBasis") (lean := "VirasoroProject.HeisenbergAlgebra.uea_eventually_commute_jgen")
*Eventual commutation in the Heisenberg universal enveloping algebra.*
Let $`a \in \UEA(\hei)` be an arbitrary element of the universal enveloping
algebra of the Heisenberg algebra $`\hei`. Then there exists a $`k_0=k_0(a) \in \bZ`
such that for all $`k \ge k_0` we have

$$`\begin{aligned}
    J_k a = a J_k .
\end{aligned}`
:::

:::proof "lem:HeisenbergEventuallyCommute"
Clear by the induction principle of the universal enveloping algebra and
Lie brackets of the Heisenberg algebra basis elements.
:::

:::lemma_ "lem:TruncationForChargedFockSpace" (uses := "def:ChargedFockSpace") (lean := "VirasoroProject.ChargedFockSpace.eventually_jgen_smul_eq_zero")
*Local truncation condition for the charged Fock space.*
Let $`\alpha \in \bbk` and let $`v \in \FockSpace^{\alpha}` be a vector in
the charged Fock space with charge $`\alpha`.
Then there exists a $`k_0 \in \bZ` such that for all $`k \ge k_0` we have

$$`\begin{aligned}
    J_k \, v = 0 .
\end{aligned}`

(In other words, the charged Fock space satisfies the local truncation condition
$`\tagHeiTrunc{}` needed for the Sugawara construction.)
:::

:::proof "lem:TruncationForChargedFockSpace" (uses := "lem:HeisenbergEventuallyCommute")
Straightforward by {bpref "lem:HeisenbergEventuallyCommute"}[]
and the properties of the highest weight vector
(cyclicity and annihilation by the upper part).
:::

:::definition "def:ChargedFockSpaceSugawara" (uses := "lem:TruncationForChargedFockSpace, thm:SugawaraRepresentation") (lean := "VirasoroProject.ChargedFockSpace.sugawaraRepresentation, VirasoroProject.ChargedFockSpace.instModuleUniversalEnvelopingAlgebraVirasoroAlgebra")
*Virasoro action on the charged Fock space.*
The charged Fock space of charge $`\alpha`
becomes a representation of the Virasoro algebra
$`\vir` with central charge $`c = 1` via the Sugawara construction
({bpref "thm:SugawaraRepresentation"}[]).
:::

:::lemma_ "lem:VacuumHighestWeightVector" (uses := "def:ChargedFockSpaceSugawara, def:VirasoroVermaModule") (lean := "VirasoroProject.ChargedFockSpace.sugawaraRepresentation_lgen_zero_apply_vacuum, VirasoroProject.ChargedFockSpace.sugawaraRepresentation_lgen_pos_apply_vacuum, VirasoroProject.ChargedFockSpace.virasoroVermaToChargedFockSpace")
*The vacuum of the charged Fock space is a highest weight vector.*
The vacuum vector $`\FockVacuum^{\alpha}` of the charged Fock space of
charge $`\alpha \in \bbk` satisfies

$$`\begin{aligned}
    L_0 \, \FockVacuum^{\alpha} = \frac{\alpha^2}{2} \, \FockVacuum^{\alpha}
    \qquad \text{and} \qquad
    L_n \, \FockVacuum^{\alpha} = 0 \text{ for all } n > 0 .
\end{aligned}`

In particular (by the universal property of Verma modules) there exists a
Virasoro-module map

$$`\begin{aligned}
    \Verma^{c=1,h=\alpha^2/2} \to \FockSpace^{\alpha}
\end{aligned}`

such that $`\VermaHWV^{c=1,h=\alpha^2/2} \mapsto \FockVacuum^{\alpha}`.
:::

:::proof "lem:VacuumHighestWeightVector" (uses := "lem:VermaUniversalProperty")
Calculation.
:::
