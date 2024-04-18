/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Mathlib.Data.Real.Basic
import Library.Basic

math2001_init

example {x : ℚ} (hx : 3 * x = 2) : x ≠ 1 := by
  apply ne_of_lt  -- transform the goal from proving ≠ to <
  calc
    x = 3 * x / 3 := by ring
    _ = 2 / 3 := by rw [hx]
    _ < 1 := by numbers

example {y : ℝ} : y ^ 2 + 1 ≠ 0 := by
  apply ne_of_gt -- transform the goal from ≠ to >
  extra

example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a ^ 2 = 0 := by
  apply le_antisymm  -- if a <= b, and a >=b, then a = b
  calc
    a ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
    _ = 0 := by rw [h1]  -- the first subgoal a <= 0 is proved
  extra  -- the second subgoal is merely 0 <= 0 + a ^ 2

example {a b : ℝ} (h1 : a ^ 2 + b ^ 2 = 0) : a ^ 2 = 0 := by
  apply le_antisymm  -- if a <= b, and a >=b, then a = b
  calc
    a ^ 2 ≤ a ^ 2 + b ^ 2 := by extra
    _ = 0 := by rw [h1]  -- the first subgoal a <= 0 is proved
  calc
    0 ≤ 0 + a ^ 2 := by extra
    _ = a ^ 2 := by ring

/-! # Exercises -/

example {m : ℤ} (hm : m + 1 = 5) : 3 * m ≠ 6 := by
  apply ne_of_gt
  calc
    3 * m = 3 * (m + 1) - 3 := by ring
    _ = 3 * 5 - 3 := by rw [hm]
    _ = 12 := by norm_num
    _ > 6 := by norm_num

example {s : ℚ} (h1 : 3 * s ≤ -6) (h2 : 2 * s ≥ -4) : s = -2 := by
  apply le_antisymm
  calc
    s = (3 * s) / 3 := by ring
    _ ≤ - 6 / 3 := by rel [h1]
    _ = -2 := by norm_num
  calc
    s = (2 * s) / 2 := by ring
    _ ≥ - 4 / 2 := by rel [h2]
    _ = -2 := by norm_num
