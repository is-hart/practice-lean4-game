import Game.Metadata
import Game.Levels.Tutorial.L01_exact

World "Tutorial"
Level 2

Title "Rewriting Equations"

Introduction "You've learned how to use an assumption to prove/close a goal.
Now we have a goal that requires rewriting in order to be proven.
You'll notice it doesn't quite match the assumption -- the a and b are backwards!
Fix this by using the rw tactic. Type ''rw [Nat.add_comm]''.
This will rewrite the equation using the commutative property of addition.
Click on Nat.add_comm under theorems/basic arithmetic in your inventory for more info."

Statement (a b : Nat) (h : b + a = 5) : (a + b = 5) := by
  rw [Nat.add_comm]
  exact h

Conclusion "Good job!"

/-- Use rw to rewrite an equation.
Following rw, type the theorem you'd like to use to rewrite the equation surrounded by square brackets.
You may use several theorems separated by commas.
You may type "repeat rw" followed by the theorem in square brackets to rewrite as many times as possible.
You may type ← before any theorems to reverse the input and output.--/

TacticDoc rw
NewTactic rw

/-- a + b = b + a --/
TheoremDoc Nat.add_comm as "add_comm" in "Basic Arithmetic"
NewTheorem Nat.add_comm
-- NewDefinition Nat Add Eq
