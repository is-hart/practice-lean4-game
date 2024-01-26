import Game.Metadata
import Game.Levels.EvenOdd.L06_mul_odd
import Mathlib.Tactic

World "EvenOdd"
Level 7

Title "Multiplying odd numbers"

/-- An even number minus an even number is even. -/
TheoremDoc sub_evens as "sub_evens" in "Even/Odd"

Introduction "Subtraction this time. I know this is getting a bit repetetive,
but it will be nice to have for the boss level!"

Statement sub_evens (a b : Nat) (h1 : even a) (h2 : even b) : even (a - b) := by
  cases' h1 with n hn
  cases' h2 with m hm
  rw [hn, hm, ← Nat.mul_sub_left_distrib]
  use (n - m)
