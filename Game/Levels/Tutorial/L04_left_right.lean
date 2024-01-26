import Game.Metadata
import Game.Levels.Tutorial.L03_rw_backwards

World "Tutorial"
Level 4

Title "Left and Right"

Introduction "In this level we are presented with an or statement.
Or is denoted by ∨ (type \\or). To prove an or statement, you must prove that one side is true.
You can choose which side to prove by using the left and right tactics. Try it out.
(Often only one side will be provable.)
Notice you've unlocked Nat.mul_add and Nat.add_mul, which are the distributive property.
If you're not sure which one to use, click on them in your inventory for more details."

Statement (a b c : Nat) (h : a * (b + c) = 3) : (a * c + b * c = 3 ∨ a * b + a * c = 3) := by
  right
  rw [← Nat.mul_add]
  exact h

Conclusion "Good job! That level was slightly trickier, however this is just the beginning!"

/-- When presented with an or statement as a goal, use right to change your goal
to the right side of the or statement. --/
TacticDoc right

/-- When presented with an or statement as a goal, use left to change your goal
to the left side of the or statement. --/
TacticDoc left

NewTactic right left

/-- a * (b + c) = a * b + a * c -/
TheoremDoc Nat.mul_add as "Nat.mul_add" in "Basic Arithmetic"

/-- (a + b) * c = a * c + b * c -/
TheoremDoc Nat.add_mul as "Nat.add_mul" in "Basic Arithmetic"

NewTheorem Nat.mul_add Nat.add_mul
