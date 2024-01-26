import Game.Metadata
import Game.Levels.EvenOdd.L01_zero_even

World "EvenOdd"
Level 2

Title "One is Odd"

/-- One is odd. -/
TheoremDoc one_odd as "one_odd" in "Even/Odd"


Introduction "Can you figure it out? Again, the definition of odd can help!"

Statement one_odd : (odd 1) := by
  use 0

Conclusion "Great work! Time to move on to more complicated levels."
