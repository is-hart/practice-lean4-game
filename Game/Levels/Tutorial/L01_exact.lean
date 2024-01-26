import Game.Metadata

World "Tutorial"
Level 1

Title "First Steps"

Introduction "We'll start simple. Everything you do will be done by tactics. You can view your unlocked tactics on the right.
Your first tactic is exact. Use this tactic to complete a goal when a goal matches an assumption.
An assumption for this level is that x = 1 (see the center of the screen), and your goal is to prove that x = 1.
Can you complete your goal?"

Statement (x : Nat) (h : x = 1) : (x = 1) := by
  exact h

Conclusion "Perfect! You've solved your first level.
Each of these levels will be working with natural numbers (ℕ).
The basic definition of these is either 0 or succ (ℕ).
succ is the successor of a natural number.
For more information on natural numbers, play the natural number game."

/- Use these commands to add items to the game's inventory. -/

/-- Use exact to close a goal when it matches an assumption.
Type "exact assumptionName" -/

TacticDoc exact
NewTactic exact

/-- A natural number. Either 0 or succ (ℕ). --/
DefinitionDoc Nat as "ℕ"

NewDefinition Nat
