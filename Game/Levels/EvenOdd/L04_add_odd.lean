import Game.Metadata
import Game.Levels.EvenOdd.L03_add_even
import Mathlib.Tactic

World "EvenOdd"
Level 4

Title "Adding odd numbers"

/-- add_odds (a b : Nat) (h1 : odd a) (h2 : odd b) : even (a + b)
An odd number plus an odd number is an even number. --/
TheoremDoc add_odds as "add_odds" in "Odd/Even"


Introduction "We already added even numbers. Now let's add odd ones!
Turns out they make even when added together also. This proof will be very similar to the last one.
(Hint: what tactic should you use if you're stuck with a messy equation?)"

Statement add_odds (a b : Nat) (h1 : odd a) (h2 : odd b) : even (a + b) := by
  cases' h1 with n hn
  cases' h2 with m hm
  rw [hn, hm]
  use (n + m + 1)
  ring_nf

Conclusion "Nice."
