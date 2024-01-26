import Game.Metadata
import Game.Levels.ThreevenThrodd.L07_sub_throver
import Mathlib.Tactic

World "ThreevenThrodd"
Level 8

Title "Subtracting Thrunders"

/-- thrunder - thrunder = threeven --/
TheoremDoc sub_thrunders as "sub_thrunders" in "Threeven/Throdd"


Introduction "You'll need a bunch of rewrites for this level."

Statement sub_thrunders (a b : Nat) (h1 : thrunder a) (h2 : thrunder b) : (threeven (a - b)) := by
  cases' h1 with c h3
  cases' h2 with d h4
  rw [h3, h4]
  ring_nf
  rw [← Nat.sub_sub, Nat.add_comm, Nat.add_sub_cancel, ← Nat.mul_sub_right_distrib, Nat.mul_comm]
  use (c - d)
