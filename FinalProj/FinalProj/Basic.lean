import Mathlib.Probability.Notation
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.UniformOn -- not CondCount
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Expect

open ProbabilityTheory
open MeasureTheory
open BigOperators -- for expectation over finsets

section GeneralProb

variable {Ω : Type*} [MeasurableSpace Ω] {s : Set Ω}
variable [MeasurableSingletonClass Ω]
variable {s t u : Set Ω}

/- The probability of any single element in a uniform distribution
over a (finite) set s is equal to (1 / #s). -/
theorem uniformOn_elem (e : Ω) (he : e ∈ s) :
  uniformOn s {e} = 1 / (Measure.count s) := by
  have he1 : Measure.count {e} = 1 := by exact Measure.count_singleton e
  simp [uniformOn, cond_apply']
  have he_sub_s : {e} ⊆ s := by
    simp [he]
  rw [(Iff.mpr Set.inter_eq_right) he_sub_s]
  rw [he1]
  simp

end GeneralProb


def DiceSpace : Finset ℕ := {1, 2, 3, 4, 5, 6}
-- alternative definitions I tried: (and got pretty confused about using Finsets versus Sets)

/-
def DiceType : Type := {n : ℕ // n ∈ ({1, 2, 3, 4, 5, 6} : Set ℕ)}
def DiceSpace'' : Set ℕ := {n | n ∈ [1, 2, 3, 4, 5, 6]}
def DiceSpace' : Finset ℕ := {1, 2, 3, 4, 5, 6}

def a : Set ℕ := (↑DiceSpace' : Set ℕ)
theorem DiceSpace_coe : a = DiceSpace :=  by
  rw [a, DiceSpace', DiceSpace]

example : Set.Finite (↑(Finset.range 7) : Set ℕ) := by
  norm_cast
  exact Set.finite_Iio 7

theorem DiceSpace_Type : (Set.univ DiceType) = DiceSpace' := sorry -- errors - huhh?

instance : Decidable (∀n : ℕ, n ∈ DiceSpace) := by
  cases Decidable with
  | isFalse hNot => intro N
  | isTrue hTrue => sorry
-/

theorem DiceSpace_finite : Set.Finite ({1, 2, 3, 4, 5, 6} : Set ℕ) := by
  have hFinset_eq_Set : ∀ x : ℕ, x ∈ ({1, 2, 3, 4, 5, 6} : Finset ℕ) ↔ x ∈ ({1, 2, 3, 4, 5, 6} : Set ℕ) := by
    simp
  exact Set.Finite.ofFinset ({1, 2, 3, 4, 5, 6} : Finset ℕ) hFinset_eq_Set

theorem DiceSpace_size : ↑DiceSpace.card = (6 : ℚ≥0) := by
  norm_cast

theorem one_in_DiceSpace : 1 ∈ (↑DiceSpace : Set ℕ) := by
  rw [DiceSpace]
  decide

noncomputable def Px : Measure ℕ := uniformOn DiceSpace -- counting measure on the space, directly
noncomputable def Px' : ℕ → ENNReal := λx ↦ pdf.uniformPDF DiceSpace x Px -- pdf (= probability of a point, here) on the space

/-
-- already defined, so don't need to show:
instance : MeasurableSpace ℕ := by exact Nat.instMeasurableSpace
instance : MeasurableSingletonClass ℕ := by exact Nat.instMeasurableSingletonClass
-/

-- instance : MeasurableSet ({1, 2, 3, 4, 5, 6} : Set ℕ) := by simp
theorem hMeasurable_dice : MeasurableSet ({1, 2, 3, 4, 5, 6} : Set ℕ) := by simp

#check Measure.count_apply hMeasurable_dice
#check Set.indicator_apply
#check (Set.indicator_apply DiceSpace (fun _ ↦ 1) 1)

theorem one_prob_eq_sixth :
  Px {1} = 1 / 6 := by
  rw [Px] --, uniformOn, Measure.count, Measure.sum]
  simp [uniformOn_elem 1 one_in_DiceSpace]
  simp [DiceSpace]

/-
-- Expectation has not been defined in the probability section of mathlib,
-- so these are some options
set_option quotPrecheck false -- not sure if this is safe
local notation " E " p => ∑' (i : ℕ), p {i} -- measure version of expectation
local notation " E' " p => ∑' (i : ℕ), p i -- pdf version of expectation
local notation " E' " p => ∑ i in (Finset.range 7), i * (p i) -- dice-specific expectation

-- dice-specific verison of expectation as a function
noncomputable def E' (p : ℕ → ENNReal) : ENNReal :=
  ∑ i in (Finset.range 7), i * (p i)
-/

noncomputable def E_dice (p : ℕ → ℚ≥0) : ℚ≥0 :=
  𝔼 i ∈ DiceSpace, p i

#check Finset.range 7

noncomputable def f_one_roll : ℕ → ℚ≥0 := (λ x ↦ x) -- identity function.
-- We want 𝔼_unif [X], and finset expect gives 𝔼_unif [f(X)], so identity for the
-- expectation of one roll should be the identity.

#check (inv_mul_eq_iff_eq_mul)

theorem one_roll_expectation_eq_three_and_a_half :
  𝔼 i ∈ DiceSpace, f_one_roll i = 7 / 2 := by
  simp [Finset.expect, f_one_roll, DiceSpace_size, DiceSpace]
  ring
  refine (IsUnit.inv_mul_eq_iff_eq_mul ?_).mpr ?_
  { simp }
  {
    refine NNRat.ext_iff.mpr ?_
    simp
    linarith
  }


-- **Problem: Find the expected number of rolls until you roll the first 6.**

-- The first 6 can occur on the {1st, 2nd, 3rd, ...} roll.
def first_six_space : Type := ℕ+
-- In order to avoid defining the identity coercion and whatnot,
-- I'll just use ℕ+ below. Keep in mind that this refers to the set of
-- possible numbers of rolls (before rolling a 6).

/-
-- I also defined the following type for the possible numbers of rolls
-- before realizing that mathlib already has the ℕ+ type.

def first_six_space : Type := {n : ℕ // n > 0}

instance : Coe first_six_space ℕ := ⟨Subtype.val⟩

theorem first_six_space.mk_coe (n : ℕ) (hN : n > 0) :
  ↑(⟨n, hN⟩ : first_six_space) = n := by rfl
-/

-- We do, however, need to define an instance of raising a ℚ to a ℕ+,
-- which is not in mathlib:
def pow (b : ℚ) : ℕ+ → ℚ :=
  λx ↦  b ^ (↑x : ℕ)

variable {b : ℚ}
#check b ^ 2

instance : HPow ℚ ℕ+ ℚ where
  hPow := pow


-- The probability of rolling a 6 on the nth roll is (5/6)^{n-1} * (1/6)
def P_first6 : ℕ+ → ℚ := λ n ↦ (5 / 6) ^ (n - 1) * (1 / 6)

/-
-- The below is irrelevant since we can't use Finset.expect on an infinite sample space
-- such as first_six_space.

-- Since Finset.expect is only equal to 𝔼_unif[f(X)], and we want 𝔼_{P_first6}[f(X)],
-- we have to define this function P * f, because 𝔼_P[f(X)] = 𝔼_unif[P(X) * f(X)]
-- = ∑ x * P(x).
def P_times_f_first6 : ℕ → ℚ≥0 := λ x ↦ x * P_first6 x
-/

theorem sum_geometric_times_n (r : ℚ) (hr : r < 1) : ∑' (i : ℕ+), i * (r ^ i) = r / (1 - r)^2 :=
  by sorry

-- Then we can calculate the expectation of the number of rolls until the first 6 appears.
theorem rolls_until_six_expectation_eq_six :
  ∑' (i : ℕ+), i * P_first6 i = 6 := by
  simp only [P_first6]
  have move_const_out : ∑' (i : ℕ+), (↑↑i : ℚ) * ((5 / 6) ^ (↑i - 1) * (1 / 6)) = (1 / 6) * ∑' (i : ℕ+), ↑↑i * (((5 / 6) : ℚ) ^ (↑i - 1)) := by
    sorry
  rw [move_const_out]
  have mult_six_fifths : (1 / 6) * ∑' (i : ℕ+), ↑↑i * ((5 / 6) : ℚ) ^ (i - 1) = (6 / 5) * (1 / 6) * ∑' (i : ℕ+), ↑↑i * ((5 / 6) : ℚ) ^ i := by
    sorry
  rw [mult_six_fifths]
  rw [sum_geometric_times_n (5 / 6) (by linarith)] -- use the sum formula
  ring


#check rolls_until_six_expectation_eq_six
