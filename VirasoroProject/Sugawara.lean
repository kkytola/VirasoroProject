/-
Copyright (c) 2025 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
import VirasoroProject.VirasoroAlgebra

/-!
# The bosonic Sugawara construction
-/

namespace VirasoroProject

section Sugawara_boson

open Filter

variable {𝕜 : Type*} [Field 𝕜]
variable {V : Type*} [AddCommGroup V] [Module 𝕜 V]

/-- Commutator `[A,B] := AB-BA` of two linear operators `A`, `B`. -/
def commutator (A B : V →ₗ[𝕜] V) : V →ₗ[𝕜] V := A * B - B * A

/-- `[A,B] = -[B,A]` -/
lemma commutator_comm (A B : V →ₗ[𝕜] V) :
    commutator A B = - commutator B A := by
  simp [commutator]

/-- `[AB,C] = A[B,C] + [A,C]B` -/
lemma commutator_pair (A B C : V →ₗ[𝕜] V) :
    commutator (A * B) C = A * (commutator B C) + (commutator A C) * B := by
  simp [commutator, sub_mul, mul_sub, ← mul_assoc]

variable (heiOper : ℤ → (V →ₗ[𝕜] V))
variable (heiTrunc : ∀ v, atTop.Eventually (fun l ↦ (heiOper l) v = 0))
variable (heiComm : ∀ k l,
  commutator (heiOper k) (heiOper l) = if k + l = 0 then (k : 𝕜) • 1 else 0)

section normal_ordered_pair

/-- Normal ordered pair of two operators:
`pairNO k l` equals `(heiOper l) ∘ (heiOper k)` if `l ≤ k`,
and `(heiOper k) ∘ (heiOper l)` otherwise. -/
def pairNO (k l : ℤ) : (V →ₗ[𝕜] V) :=
  if l ≤ k then ((heiOper l) ∘ₗ (heiOper k)) else ((heiOper k) ∘ₗ (heiOper l))

/-- Alternative normal ordered pair of two operators:
`pairNO' k l` equals `(heiOper l) ∘ (heiOper k)` if `k ≥ 0`,
and `(heiOper k) ∘ (heiOper l)` otherwise. -/
def pairNO' (k l : ℤ) : (V →ₗ[𝕜] V) :=
  if 0 ≤ k then ((heiOper l) ∘ₗ (heiOper k)) else ((heiOper k) ∘ₗ (heiOper l))

include heiComm

/-- `heiOper k` and `heiOper l` commute unless `k = l`. -/
lemma heiComm_of_add_ne_zero {k l : ℤ} (hkl : k + l ≠ 0) :
    (heiOper k) ∘ₗ (heiOper l) = (heiOper l) ∘ₗ (heiOper k) := by
  simpa [hkl, sub_eq_zero, commutator] using heiComm k l

/-- The two definitions of normal ordered pairs coincide. -/
lemma heiOper_pairNO_eq_pairNO' (k l : ℤ) :
    pairNO heiOper k l = pairNO' heiOper k l := by
  unfold pairNO pairNO'
  by_cases hk : 0 ≤ k
  · simp only [hk, ↓reduceIte, ite_eq_left_iff, not_le]
    intro hkl
    apply heiComm_of_add_ne_zero _ heiComm
    exact ne_of_gt (by linarith)
  · simp only [hk, ↓reduceIte, ite_eq_right_iff]
    intro hlk
    apply heiComm_of_add_ne_zero _ heiComm
    exact ne_of_lt (by linarith)

omit heiComm

/-- `pairNO k l` is symmetric in `k` and `l`. -/
lemma heiOper_pairNO_symm (k l : ℤ) :
    pairNO heiOper k l = pairNO heiOper l k := by
  unfold pairNO
  by_cases heq : l = k
  · rw [heq]
  by_cases hlk : l ≤ k
  · have hkl : ¬ k ≤ l := by linarith [lt_of_le_of_ne hlk heq]
    simp [hlk, hkl]
  · have hkl : k ≤ l := by linarith
    simp [hlk, hkl]

include heiComm

lemma heiOper_pairNO'_symm (k l : ℤ) :
    pairNO' heiOper k l = pairNO' heiOper l k := by
  simpa [← heiOper_pairNO_eq_pairNO' _ heiComm] using heiOper_pairNO_symm heiOper k l

omit heiComm
include heiTrunc

-- Maybe this one is not the most useful; want to fix the sum of indices.
lemma heiPairNO_trunc (k : ℤ) (v : V) :
    atTop.Eventually (fun l ↦ pairNO heiOper k l v = 0) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (heiTrunc v)
  filter_upwards [Ici_mem_atTop N] with l hl
  rw [Set.mem_Ici] at hl
  by_cases hlk : l ≤ k
  · simp [pairNO, hlk, hN _ (show N ≤ k by linarith)]
  · simp [pairNO, hlk, hN _ hl]

lemma heiPairNO_trunc_atTop_sub (n : ℤ) (v : V) :
    atTop.Eventually (fun k ↦ pairNO heiOper (n-k) k v = 0) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (heiTrunc v)
  filter_upwards [Ici_mem_atTop N] with l hl
  rw [Set.mem_Ici] at hl
  by_cases hln : l ≤ n-l
  · simp [pairNO, hln, hN _ (show N ≤ n-l by linarith)]
  · simp [pairNO, hln, hN _ (show N ≤ l by linarith)]

lemma heiPairNO_trunc_atBot_sub (n : ℤ) (v : V) :
    atBot.Eventually (fun k ↦ pairNO heiOper (n-k) k v = 0) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (heiTrunc v)
  filter_upwards [Iic_mem_atBot (n-N)] with l hl
  rw [Set.mem_Iic] at hl
  by_cases hln : l ≤ n-l
  · simp [pairNO, hln, hN _ (show N ≤ n-l by linarith)]
  · simp [pairNO, hln, hN _ (show N ≤ l by linarith)]

lemma heiPairNO_trunc_cofinite_sub (n : ℤ) (v : V) :
    cofinite.Eventually (fun k ↦ pairNO heiOper (n-k) k v = 0) := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp (heiPairNO_trunc_atTop_sub heiOper heiTrunc n v)
  obtain ⟨B, hB⟩ := eventually_atBot.mp (heiPairNO_trunc_atBot_sub heiOper heiTrunc n v)
  have filt : (Set.Ioo B T)ᶜ ∈ cofinite :=
    Set.Finite.compl_mem_cofinite (show (Set.Ioo B T).Finite from Set.finite_Ioo B T)
  filter_upwards [filt] with k hkBT
  simp only [Set.mem_compl_iff, Set.mem_Ioo, not_and, not_lt] at hkBT
  by_cases hk : k ≤ B
  · exact hB k hk
  · exact hT k (hkBT (Int.lt_of_not_ge hk))

include heiComm

/-- `[(heiOper l) ∘ (heiOper k), (heiOper m)] = -m * (δ[k+m=0] + δ[l+m=0]) • heiOper (k + l + m)` -/
lemma commutator_heiPair_heiGen (l k m : ℤ) :
    commutator ((heiOper l) * (heiOper k)) (heiOper m)
      = ((-m : 𝕜) * ((if k + m = 0 then 1 else 0)
               + (if l + m = 0 then 1 else 0))) • heiOper (k + l + m) := by
  simp [commutator_pair, heiComm]
  by_cases hkm : k + m = 0
  · have k_eq : k = -m := by linarith
    simp [k_eq]
    by_cases hlm : l + m = 0
    · have l_eq : l = -m := by linarith
      simp [l_eq, mul_add, add_smul]
    · simp [hlm]
  · simp [hkm]
    by_cases hlm : l + m = 0
    · have l_eq : l = -m := by linarith
      simp [l_eq]
    · simp [hlm]

end normal_ordered_pair -- section

section central_charge_calculation

open Finset

/-- A discrete integral of a function on `ℕ`. -/
def nPrimitive {R : Type*} [AddCommMonoid R] (f : ℕ → R) (n : ℕ) : R := match n with
  | 0 => (0 : R)
  | n + 1 => nPrimitive f n + f n

@[simp] lemma nPrimitive_zero {R : Type*} [AddCommMonoid R] (f : ℕ → R) :
    nPrimitive f 0 = 0 :=
  rfl

@[simp] lemma nPrimitive_succ {R : Type*} [AddCommMonoid R] (f : ℕ → R) (n : ℕ) :
    nPrimitive f (n + 1) = nPrimitive f n + f n :=
  rfl

lemma nPrimitive_eq_sum {R : Type*} [AddCommMonoid R] (f : ℕ → R) (n : ℕ) :
    nPrimitive f n = ∑ j in range n, f j := by
  induction' n with n ih
  · simp
  · simp [nPrimitive_succ, sum_range_succ, ih]

/-- A discrete integral of a function on `ℤ`. -/
def zPrimitive {R : Type*} [AddCommGroup R] (f : ℤ → R) (n : ℤ) : R :=
  if 0 ≤ n then ∑ j in range (Int.toNat n), f j else -(∑ j in range (Int.natAbs n), f (-j-1))

@[simp] lemma zPrimitive_zero {R : Type*} [AddCommGroup R] (f : ℤ → R) :
    zPrimitive f 0 = 0 :=
  rfl

@[simp] lemma zPrimitive_apply_of_nonneg {R : Type*} [AddCommGroup R] (f : ℤ → R)
    {n : ℤ} (hn : 0 ≤ n) :
    zPrimitive f n = ∑ j in range (Int.toNat n), f j := by
  simp [zPrimitive, hn]

@[simp] lemma zPrimitive_apply_of_nonpos {R : Type*} [AddCommGroup R] (f : ℤ → R)
    {n : ℤ} (hn : n ≤ 0) :
    zPrimitive f n = -(∑ j in range (Int.natAbs n), f (-j-1)) := by
  by_cases hn' : n = 0
  · simp [hn']
  · simp [zPrimitive, lt_of_le_of_ne hn hn']

@[simp] lemma zPrimitive_succ {R : Type*} [AddCommGroup R] (f : ℤ → R) (n : ℤ) :
    zPrimitive f (n + 1) = zPrimitive f n + f n := by
  by_cases hn : 0 ≤ n
  · simp [zPrimitive, hn, Int.le_add_one hn, Int.toNat_add hn zero_le_one, sum_range_succ]
  · simp only [not_le] at hn
    have n_natAbs : n.natAbs = (n+1).natAbs + 1 := by
      simpa using Int.natAbs_add_of_nonpos (b := -1) hn (Int.toNat_eq_zero.mp rfl)
    simp only [zPrimitive_apply_of_nonpos _ hn, zPrimitive_apply_of_nonpos _ hn.le, n_natAbs,
               sum_range_succ, Int.natCast_natAbs, neg_add_rev]
    simp only [add_comm (-(f _)), add_assoc, self_eq_add_right]
    simp [show -|n + 1| - 1 = n by rw [abs_of_nonpos hn, neg_neg] ; ring]

lemma eq_zPrimitive_of_eq_zero_of_forall_eq_add {R : Type*} [AddCommGroup R] {f F : ℤ → R}
    (h0 : F 0 = 0) (h1 : ∀ n, F (n + 1) = F n + f n) :
    F = zPrimitive f := by
  have obsP : ∀ (n : ℕ), F n = zPrimitive f n := by
    intro n
    induction' n with n ih
    · simp [h0]
    · have keyF := h1 n
      have keyP := zPrimitive_succ f n
      norm_cast at *
      rw [keyF, ih, ← keyP]
  have obsM : ∀ (n : ℕ), F (-n) = zPrimitive f (-n) := by
    intro n
    induction' n with n ih
    · simp [h0]
    · have keyF := h1 (-(n + 1))
      have keyP := zPrimitive_succ f (-(n + 1))
      simp only [Int.natAbs_neg, Int.natAbs_ofNat, neg_add_rev, Int.reduceNeg,
                 neg_add_cancel_comm, Nat.cast_add, Nat.cast_one] at ih keyF keyP ⊢
      rw [keyF, keyP] at ih
      exact add_right_cancel_iff.mp ih
  ext m
  by_cases hm : 0 ≤ m
  · rw [(Int.toNat_of_nonneg hm).symm]
    exact obsP m.toNat
  · have hm' : m < 0 := Int.lt_of_not_ge hm
    rw [show m = -m.natAbs from Int.eq_neg_comm.mp (by simpa [hm'] using hm'.le)]
    exact obsM m.natAbs

lemma zPrimitive_add {R : Type*} [AddCommGroup R] (f g : ℤ → R) :
    zPrimitive (f + g) = zPrimitive f + zPrimitive g  := by
  apply (eq_zPrimitive_of_eq_zero_of_forall_eq_add ..).symm
  · simp
  · intro n
    simp only [Pi.add_apply, zPrimitive_succ]
    ac_rfl

lemma zPrimitive_smul {R S : Type*} [AddCommGroup R] [DistribSMul S R]
    (c : S) (f : ℤ → R) :
    zPrimitive (c • f) = c • (zPrimitive f) := by
  apply (eq_zPrimitive_of_eq_zero_of_forall_eq_add ..).symm <;> simp

lemma zPrimitive_sub {R : Type*} [AddCommGroup R] (f g : ℤ → R) :
    zPrimitive (f - g) = zPrimitive f - zPrimitive g  := by
  apply (eq_zPrimitive_of_eq_zero_of_forall_eq_add ..).symm
  · simp
  · intro n
    --simp only [Pi.sub_apply, zPrimitive_succ, sub_sub]
    --ac_rfl
    sorry

lemma zPrimitive_mul_left {R : Type*} [Ring R] (c : R) (f : ℤ → R) :
    zPrimitive (fun n ↦ c * f n) = fun n ↦ c * zPrimitive f n := by
  apply (eq_zPrimitive_of_eq_zero_of_forall_eq_add ..).symm
  · simp
  · intro n
    simp [mul_add]

lemma zPrimitive_mul_right {R : Type*} [Ring R] (c : R) (f : ℤ → R) :
    zPrimitive (fun n ↦ f n * c) = fun n ↦ zPrimitive f n * c := by
  apply (eq_zPrimitive_of_eq_zero_of_forall_eq_add ..).symm
  · simp
  · intro n
    simp [add_mul]

def zMonomialF (R : Type*) [AddCommGroup R] [One R] (d : ℕ) : ℤ → R := match d with
  | 0 => fun _ ↦ 1
  | d + 1 => zPrimitive (zMonomialF R d)

lemma zMonomialF_eq (R : Type) [Field R] [CharZero R] (d : ℕ) :
    (zMonomialF R d) = (fun (n : ℤ) ↦ ((∏ j in range d, (n - j : R)) / (Nat.factorial d : R))) := by
  induction' d with d ihd
  · funext n
    simp [zMonomialF]
  rw [zMonomialF, Eq.comm]
  apply eq_zPrimitive_of_eq_zero_of_forall_eq_add
  · simp only [Int.cast_zero, zero_sub, prod_div_distrib, prod_const, card_range, div_eq_zero_iff,
               ne_eq, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
               pow_eq_zero_iff, Nat.cast_eq_zero]
    left
    exact prod_eq_zero_iff.mpr ⟨0, by simp, by simp⟩
  · intro n
    simp only [Int.cast_add, Int.cast_one] at *
    simp [ihd]
    rw [prod_range_succ, prod_range_succ]
    --have := Nat.factorial_ne_zero d
    --have := Nat.factorial_ne_zero (d + 1)
    sorry

lemma zMonomialF_zero_eq (R : Type) [Field R] [CharZero R] (d : ℕ) (n : ℤ) :
    zMonomialF R 0 n = 1 := by
  simp [zMonomialF]

lemma zMonomialF_one_eq (R : Type) [Field R] [CharZero R] (n : ℤ) :
    zMonomialF R 1 n = n := by
  simp [zMonomialF_eq]

lemma zMonomialF_two_eq (R : Type) [Field R] [CharZero R] (n : ℤ) :
    zMonomialF R 2 n = n * (n - 1) / 2 := by
  simp [zMonomialF_eq, prod_range_succ]

lemma zMonomialF_three_eq (R : Type) [Field R] [CharZero R] (n : ℤ) :
    zMonomialF R 3 n = n * (n - 1) * (n - 2) / 6 := by
  simp [zMonomialF_eq, prod_range_succ, show Nat.factorial 3 = 6 from rfl]

lemma zMonomialF_four_eq (R : Type) [Field R] [CharZero R] (n : ℤ) :
    zMonomialF R 4 n = n * (n - 1) * (n - 2) * (n - 3) / 24 := by
  simp [zMonomialF_eq, prod_range_succ, show Nat.factorial 4 = 24 from rfl]

lemma zMonomialF_five_eq (R : Type) [Field R] [CharZero R] (n : ℤ) :
    zMonomialF R 5 n = n * (n - 1) * (n - 2) * (n - 3) * (n - 4) / 120 := by
  simp [zMonomialF_eq, prod_range_succ, show Nat.factorial 5 = 120 from rfl]

lemma zMonomialF_apply_eq_zero_of_of_nonneg_lt (R : Type) [Field R] [CharZero R]
    (d : ℕ) {n : ℕ} (n_lt : n < d) :
    zMonomialF R d n = 0 := by
  simp only [zMonomialF_eq R d, Int.cast_natCast, div_eq_zero_iff, Nat.cast_eq_zero]
  exact Or.inl <| prod_eq_zero_iff.mpr ⟨n, ⟨mem_range.mpr n_lt, by simp⟩⟩

lemma bosonic_sugawara_cc_calc (n : ℤ) :
    zPrimitive (fun l ↦ (l : ℚ) * (n - l)) n = (n^3 - n) / 6 := by
  have obs : (n^3 - n) / 6 = (n - 1 : ℚ) * zMonomialF ℚ 2 n - 2 * zMonomialF ℚ 3 n := by
    rw [zMonomialF_two_eq, zMonomialF_three_eq]
    field_simp
    ring
  have key : (zPrimitive fun l ↦ (n - 1 : ℚ) * l) - (zPrimitive fun l ↦ 2 * zMonomialF ℚ 2 l)
              = zPrimitive ((fun (l : ℤ) ↦ (l : ℚ) * (n - l))) := by
    rw [← zPrimitive_sub]
    apply congr_arg zPrimitive
    ext l
    simp [zMonomialF_two_eq]
    ring
  simp_rw [obs, ← key, zPrimitive_mul_left]
  dsimp
  congr
  ext m
  rw [zMonomialF_one_eq]

lemma bosonic_sugawara_cc_calc_nat (n : ℕ) :
    ∑ l ∈ Finset.range n, (l : ℚ) * (n - l) = (n^3 - n) / 6 := by
  have key := bosonic_sugawara_cc_calc n
  simp only [Int.cast_natCast, Nat.cast_nonneg, zPrimitive_apply_of_nonneg, Int.toNat_ofNat] at key
  rw [← key]

end central_charge_calculation

end Sugawara_boson -- section

end VirasoroProject -- namespace
