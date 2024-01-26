import Game.Metadata
import Game.Levels.ThreevenThrodd.L06_sub_threeven
import Mathlib.Tactic

World "ThreevenThrodd"
Level 7

Title "Subtracting Throvers"

/-- throver - throver = threeven --/
TheoremDoc sub_throvers as "sub_throvers" in "Threeven/Throdd"


Introduction "This level is a bit tricky!"

Statement sub_throvers (a b : Nat) (h1 : throver a) (h2 : throver b) : (threeven (a - b)) := by
  cases' h1 with c h3
  cases' h2 with d h4
  rw [h3, h4]
  ring_nf
  use c - d
  rw [← Nat.sub_sub (1 + c * 3) 1 (d * 3), Nat.add_comm, Nat.add_one_sub_one]
  ring_nf
  rw [Nat.mul_sub_right_distrib]
