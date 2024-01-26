import Game.Metadata
import Game.Levels.ThreevenThrodd.L04_mul_thrunder
import Mathlib.Tactic

World "ThreevenThrodd"
Level 5

Title "Multiplying threevens"

/-- thrunder * throver = thrunder --/
TheoremDoc mul_thrunder_throver as "mul_thrunder_throver" in "Threeven/Throdd"


Introduction "Nothing too crazy here."

Statement mul_thrunder_throver (a b : Nat) (h1 : thrunder a) (h2 : throver b) : (thrunder (a * b)) := by
  cases' h1 with c h3
  cases' h2 with d h4
  rw [h3, h4]
  ring_nf
  use (c + d * 2 + c * d * 3)
  ring_nf
