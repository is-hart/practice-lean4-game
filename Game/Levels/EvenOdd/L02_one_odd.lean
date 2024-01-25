import Game.Metadata
import Game.Levels.EvenOdd.L01_zero_even

World "EvenOdd"
Level 2

Title "One is Even"

/-- One is odd. --/
TheoremDoc one_odd as "one_odd" in "Odd/Even"


Introduction "Let's start off simple and show that the number zero is even.

To do this, we need to find a number that doubles to make zero. We can use the ``use'' tactic to tell Lean to use that number. Try it out!"

Statement one_odd : (even 0) := by
  use 0

Conclusion "Great work!"
