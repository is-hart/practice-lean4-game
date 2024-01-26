import Game.Metadata
import Game.Levels.ThreevenThrodd.L01_threeven_zero
import Mathlib.Tactic

World "ThreevenThrodd"
Level 2

Title "Multiplying threevens"

/-- Threeven * Threeven = Threeven --/
TheoremDoc mul_threevens as "mul_threevens" in "Threeven/Throdd"


Introduction "We're going straight to multiplication this time.
Let's prove that the product of two threevens is a threeven."

Statement mul_threevens (a b : Nat) (h1 : threeven a) (h2 : threeven b) : (threeven (a * b)) := by
  cases' h1 with c h3
  cases' h2 with d h4
  rw [h3, h4, Nat.mul_assoc, Nat.mul_comm c]
  use (3 * d * c)
