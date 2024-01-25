import Game.Metadata

World "EvenOdd"
Level 1

Title "First Steps"

def even (a : Nat) := ∃ n : Nat, a = 2 * n
def odd (a : Nat) := ∃ n : Nat, a = 2 * n + 1

/-- Zero is even. --/
TheoremDoc zero_even as "zero_even" in "Odd/Even"


Introduction "Let's start off simple and show that the number zero is even.

To do this, we need to find a number that doubles to make zero. We can use the ``use'' tactic to
tell Lean to use that number. Try it out!"

Statement zero_even : (even 0) := by
  use 0

Conclusion "Great work! Note that if you try to ``use'' a different value, you might get stuck with
an impossible goal."

/- Use these commands to add items to the game's inventory. -/

/-- use use use --/

TacticDoc use
NewTactic use

-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

/-- Odd numbers are one more than a multiple of two--/
DefinitionDoc odd as "odd"

/-- Even numbers are multiples of two--/
DefinitionDoc even as "even"

NewDefinition odd even
