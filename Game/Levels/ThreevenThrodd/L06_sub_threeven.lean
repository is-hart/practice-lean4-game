import Game.Metadata
import Game.Levels.ThreevenThrodd.L05_mul_thrunder_throver
import Mathlib.Tactic

World "ThreevenThrodd"
Level 6

Title "Subtracting Threevens"

/-- threeven - threeven = threeven --/
TheoremDoc sub_threevens as "sub_threevens" in "Threeven/Throdd"


Introduction "Time for subtracting. Any two numbers of the same threeven/throver/thrunder
subtracted give a threeven number. We'll start with threevens."

Statement sub_threevens (a b : Nat) (h1 : threeven a) (h2 : threeven b) : (threeven (a - b)) := by
  cases' h1 with c h3
  cases' h2 with d h4
  rw [h3, h4]
  use (c - d)
  ring_nf
  rw [Nat.mul_sub_right_distrib c d 3]
