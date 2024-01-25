import Game.Metadata

World "Tutorial"
Level 1

Title "First Steps"

Introduction "We'll start simple. Everything you do will be done by tactics. You can view your unlocked tactics on the right.
Your first tactic is exact. Use this tactic to complete a goal when a goal matches an assumption.
An assumption for this level is that x = 1 (see the center of the screen), and your goal is to prove that x = 1.
Can you complete yoru goal?"

/-- practice --/
TheoremDoc practice1 as "practice1" in "Don't Use These"

Statement practice1 (x : Nat) (h : x = 1) : (x = 1) := by
  exact h

Conclusion "Perfect! Let's continue on."

/- Use these commands to add items to the game's inventory. -/

/-- Use exact to close a goal when it matches an assumption.
Type "exact assumptionName" --/

TacticDoc exact
NewTactic exact

-- NewLemma Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
