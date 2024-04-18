/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

-- For all ∀
example {a : ℝ} (h : ∀ x, a ≤ x ^ 2 - 2 * x) : a ≤ -1 :=
  calc
    a ≤ 1 ^ 2 - 2 * 1 := by apply h
    _ = -1 := by numbers


-- For all ∀
example {n : ℕ} (hn : ∀ m, n ∣ m) : n = 1 := by
  have h1 : n ∣ 1 := by apply hn
  have h2 : 0 < 1 := by norm_num
  apply le_antisymm  -- if 1 ≤ n ≤ 1 then n = 1
  -- prove for n ≤ 1
  -- the following lemma says if b is positive and a | b then a ≤ b
  · apply Nat.le_of_dvd h2 h1
  -- prove for 1 ≤ n
  -- the following lemma says {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : 0 < a
  · apply Nat.pos_of_dvd_of_pos h1 h2


example {a b : ℝ} (h : ∀ x, x ≥ a ∨ x ≤ b) : a ≤ b := by
  -- Use a specific format of x with a and b for the forall
  have hm : (a + b) / 2 ≥ a ∨ (a + b) / 2 ≤ b := by apply h
  obtain hm | hm := hm
  · calc
    b = 2 * ((a + b) / 2) - a := by ring
    _ ≥ 2 * a - a := by rel [hm]
    _ = a := by ring
  · calc
    a = 2 * ((a + b) / 2) - b := by ring
    _ ≤ 2 * b - b := by rel [hm]
    _ = b := by ring


example {a b : ℝ}
    (ha1 : a ^ 2 ≤ 2)
    (hb1 : b ^ 2 ≤ 2)
    (ha2 : ∀ y, y ^ 2 ≤ 2 → y ≤ a)
    (hb2 : ∀ y, y ^ 2 ≤ 2 → y ≤ b) :
    a = b := by
  apply le_antisymm   -- if a ≤ b ≤ a then a = b
  -- prove a ≤ b
  · apply hb2  -- the goal becomes a ^ 2 ≤ 2
    apply ha1
  -- prove b ≤ a
  · apply ha2 -- the goal becomes b ^ 2 ≤ a
    apply hb1

example : ∃ b : ℝ, ∀ x : ℝ, b ≤ x ^ 2 - 2 * x := by
  use -1  -- use is for ∃
  intro x  -- intro is for ∀
  calc
    -1 ≤ -1 + (x - 1) ^ 2 := by extra
    _ = x ^ 2 - 2 * x := by ring

-- The following lemma is used:
-- lemma abs_le_of_sq_le_sq' (h : x ^ 2 ≤ y ^ 2) (hy : 0 ≤ y) : -y ≤ x ∧ x ≤ y
example : ∃ c : ℝ, ∀ x y, x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ c := by
  use - 3
  intro x y -- here, the goal is  ⊢ x ^ 2 + y ^ 2 ≤ 4 → x + y ≥ -3
  intro h -- now, we have h : x ^ 2 + y ^ 2 ≤ 4 and the goal is ⊢ x + y ≥ -3

  -- prove the hypothesis for the first part of the lemma to use
  have h1: (x + y) ^ 2 ≤ 3 ^ 2
  calc
    (x + y) ^ 2 ≤ (x + y) ^ 2 + (x - y) ^ 2 := by extra
    _ = 2 * (x ^ 2 + y ^ 2) := by ring
    _ ≤ 2 * 4 := by rel [h]
    _ ≤ 3 ^ 2 := by norm_num

  -- prove the hypothesis for the second part of the lemma to use
  have h2: (0 : ℝ) ≤ 3 := by norm_num

  -- since the lemma has an and in its goal so we need to split it
  obtain ⟨ hleft, hright ⟩ := abs_le_of_sq_le_sq' h1 h2  -- notice the type issue
  apply hleft



example : forall_sufficiently_large n : ℤ, n ^ 3 ≥ 4 * n ^ 2 + 7 := by
  dsimp
  use 5  -- we just need to prove the property is true for n ≥ 5 since n is sufficiently large
  intro n hn
  calc
    n ^ 3 = n * n ^ 2 := by ring
    _ ≥ 5 * n ^ 2 := by rel [hn]
    _ = 4 * n ^ 2 + n ^ 2 := by ring
    _ ≥ 4 * n ^ 2 + 5 ^ 2 := by rel [hn]
    _ = 4 * n ^ 2 + 7 + 18 := by ring
    _ ≥ 4 * n ^ 2 + 7 := by extra


-- def Prime (p : ℕ) : Prop :=
--   2 ≤ p ∧ ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p

-- the lemma Nat.le_of_dvd says if 0 < b and a | b then a ≤ b
-- the lemma Nat.pos_of_dvd_of_pos says {a b : ℕ} (hab : a ∣ b) (hb : 0 < b) : 0 < a

example : Prime 2 := by
  dsimp [Prime] -- now the goal is: 2 ≤ 2   ∧   ∀ (m : ℕ), m ∣ 2 → m = 1 ∨ m = 2
  constructor -- split the above goals into two

  -- prove that 2 ≤ 2
  · numbers -- show `2 ≤ 2`

  -- prove that ∀ (m : ℕ), m ∣ 2 → m = 1 ∨ m = 2
  intro m hmp  -- essentially m is a factor of 2, so it can either be 1 or 2
  -- now we have m: ℕ and hmp: m ∣ 2
  -- the goal is to prove m = 1 ∨ m = 2

  have hp : 0 < 2 := by norm_num
  have hmp_le : m ≤ 2 := Nat.le_of_dvd hp hmp
  have h1m : 1 ≤ m := Nat.pos_of_dvd_of_pos hmp hp
  interval_cases m
  · left -- case when m = 1
    numbers -- show `1 = 1`
  · right -- case when m = 2
    numbers -- show `2 = 2`

-- not_prime {p : ℕ} (k l : ℕ) (hk1 : k ≠ 1) (hkp : k ≠ p) (hkl : p = k * l) : ¬Prime p
example : ¬ Prime 6 := by
  apply not_prime 2 3
  · numbers -- show `2 ≠ 1`
  · numbers -- show `2 ≠ 6`
  · numbers -- show `6 = 2 * 3`

/-! # Exercises -/


example {a : ℚ} (h : ∀ b : ℚ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 :=
  sorry

example {n : ℤ} (hn : ∀ m, 1 ≤ m → m ≤ 5 → m ∣ n) : 15 ∣ n := by
  sorry

example : ∃ n : ℕ, ∀ m : ℕ, n ≤ m := by
  sorry

example : ∃ a : ℝ, ∀ b : ℝ, ∃ c : ℝ, a + b < c := by
  sorry

example : forall_sufficiently_large x : ℝ, x ^ 3 + 3 * x ≥ 7 * x ^ 2 + 12 := by
  sorry

example : ¬(Prime 45) := by
  sorry
