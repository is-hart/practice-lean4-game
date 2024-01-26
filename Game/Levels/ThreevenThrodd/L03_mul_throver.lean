import Game.Metadata
import Game.Levels.ThreevenThrodd.L02_mul_threeven
import Mathlib.Tactic

World "ThreevenThrodd"
Level 3

Title "Multiplying throvers"

/-- Throver * Throver = Throver --/
TheoremDoc mul_throvers as "mul_throvers" in "Threeven/Throdd"


Introduction "Next we'll multiply throvers. This should give us a throver.
The challenge of this level is figuring out what to ''use''.
Don't forget about ring_nf!"

Statement mul_throvers (a b : Nat) (h1 : throver a) (h2 : throver b) : (throver (a * b)) := by
  cases' h1 with c h3
  cases' h2 with d h4
  rw [h3, h4]
  use (c + d + c * d * 3)
  ring_nf

Conclusion "Here's my solution:

cases' h1 with c h3

cases' h2 with d h4

rw [h3, h4]

use (c + d + c * d * 3)

ring_nf"
