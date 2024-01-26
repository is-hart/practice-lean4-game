import Game.Metadata

World "EvenOdd"
Level 1

Title "Zero is Even"

def even (a : Nat) := ∃ n : Nat, a = 2 * n
def odd (a : Nat) := ∃ n : Nat, a = 2 * n + 1

/-- Zero is even. -/
TheoremDoc zero_even as "zero_even" in "Even/Odd"


Introduction "Let's start off simple and show that the number zero is even.
Because even and odd are existance statements, as long as there is one value which
works the statement is true. We can use the ''use'' tactic followed by a number
to choose a number which makes the statement true. Try it out here.
Check the definition of even if you're not sure what value to use."

Statement zero_even : (even 0) := by
  use 0

Conclusion "Great work! Note that if you try to use a different value, you might get stuck with
an impossible goal."

/-- When given a "there exists" statement, use the use command to use a specific value.
Because of the nature of ∃ statements, if one value works the statement is true.
Remember that even and odd are existance statements in disguise! -/
TacticDoc use
NewTactic use

-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

/-- odd (a : Nat) := ∃ n : Nat, a = 2 * n + 1

If there exists a natural number n such that one more than 2 times n is a, then a is odd. -/
DefinitionDoc odd as "odd"

/-- even (a : Nat) := ∃ n : Nat, a = 2 * n

If there exists a natural number n such that 2 times n is a, then a is even. -/
DefinitionDoc even as "even"

NewDefinition odd even
