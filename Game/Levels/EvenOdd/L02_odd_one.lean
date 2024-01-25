import Game.Metadata
import Game.Levels.EvenOdd.L01_even_zero

World "EvenOdd"
Level 2

Title "First Steps"

/-- Zero is even. --/
TheoremDoc one_odd as "one_odd" in "Odd/Even"


Introduction "Let's start off simple and show that the number zero is even.

To do this, we need to find a number that doubles to make zero. We can use the ``use'' tactic to
tell Lean to use that number. Try it out!"

Statement one_odd : (odd 1) := by
  use 0

Conclusion "Great work! Note that if you try to ``use'' a different value, you might get stuck with
an impossible goal."

/- Use these commands to add items to the game's inventory. -/
