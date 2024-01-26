import Game.Metadata
import Game.Levels.Tutorial.L02_rw

World "Tutorial"
Level 3

Title "Rewriting Backwards"

Introduction "Let's use another feature of the rw tactic to prove this level.
We're introducting a new theorem for natural numbers: associativity. This theorem is called ''Nat.add_assoc''.
This states that a + b + c = a + (b + c). Keep in mind that in lean a + b + c actually means (a + b) + c.
But what if we want to convert backwards, from a + (b + c) to a + b + c?
To do this we type a left arrow before our theorem in rw. Type ← by typing '\\l'.
Try this out!
"

Statement (a b c : Nat) (h : a + b + c = 3) : (a + (b + c) = 3) := by
  rw [← Nat.add_assoc]
  exact h

Conclusion "Great. The rw tactic can also be used in an assumption h by typing rw [theorem] at h."

/-- a + b + c = a + (b + c)

Associative property of addition-/
TheoremDoc Nat.add_assoc as "Nat.add_assoc" in "Basic Arithmetic"
NewTheorem Nat.add_assoc
-- NewDefinition Nat Add Eq
