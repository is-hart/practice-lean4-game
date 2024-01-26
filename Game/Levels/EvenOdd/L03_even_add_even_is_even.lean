import Game.Metadata
import Game.Levels.EvenOdd.L01_even_zero

World "EvenOdd"
Level 3

Title "Adding even numbers"

/-- Zero is even. --/
TheoremDoc even_plus_even_is_even as "one_odd" in "Odd/Even"


Introduction "adding even gets even its so cool."

Statement even_plus_even_is_even (a b : Nat) (h1 : even a) (h2 : even b) : even (a + b) := by
  cases' h1 with n hn
  cases' h2 with m hm
  rw [hn, hm]
  use (n + m)
  rw [Nat.mul_add]

Conclusion "Great work! Note that if you try to ``use'' a different value, you might get stuck with
an impossible goal."

/- Use these commands to add items to the game's inventory. -/

/-- rw --/

TacticDoc rw

/-- cases! --/

TacticDoc cases'

NewTactic rw cases'
