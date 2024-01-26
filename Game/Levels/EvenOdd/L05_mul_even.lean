import Game.Metadata
import Game.Levels.EvenOdd.L04_add_odd
import Mathlib.Tactic

World "EvenOdd"
Level 5

Title "Multiplying even numbers"

/-- An even number times an even number is even. -/
TheoremDoc mul_evens as "mul_evens" in "Even/Odd"


Introduction "It's time to do some multiplication! See if you can figure this one out yourself."

Statement mul_evens (a b : Nat) (h1 : even a) (h2 : even b) : even (a * b) := by
  cases' h1 with n hn
  cases' h2 with m hm
  rw [hn, hm]
  use (n * m * 2)
  ring_nf
