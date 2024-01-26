import Game.Metadata
import Game.Levels.ThreevenThrodd.L03_mul_throver
import Mathlib.Tactic

World "ThreevenThrodd"
Level 4

Title "Multiplying thrunders"

/-- thrunder * thrunder = Throver --/
TheoremDoc mul_thrunders as "mul_thrunders" in "Threeven/Throdd"


Introduction "Time for thrunders. These multiply to get throvers."

Statement mul_thrunders (a b : Nat) (h1 : thrunder a) (h2 : thrunder b) : (throver (a * b)) := by
  cases' h1 with c h3
  cases' h2 with d h4
  rw [h3, h4]
  ring_nf
  use (c * 2 + d * 2 + c * d * 3 + 1)
  ring_nf
