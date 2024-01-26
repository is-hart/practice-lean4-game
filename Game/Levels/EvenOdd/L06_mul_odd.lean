import Game.Metadata
import Game.Levels.EvenOdd.L05_mul_even
import Mathlib.Tactic

World "EvenOdd"
Level 6

Title "Multiplying odd numbers"

/-- An odd number times an odd number is odd. -/
TheoremDoc mul_odds as "mul_odds" in "Even/Odd"


Introduction "In this level, you'll need to ''use'' a long expression.
Can you figure out what it is? ring_nf can help."

Statement mul_odds (a b : Nat) (h1 : odd a) (h2 : odd b) : odd (a * b) := by
  cases' h1 with n hn
  cases' h2 with m hm
  rw [hn, hm]
  use (n + m + n * m * 2)
  ring_nf
