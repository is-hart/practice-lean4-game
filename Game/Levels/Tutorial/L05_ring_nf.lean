import Game.Metadata
import Game.Levels.Tutorial.L04_left_right
import Mathlib.Tactic

World "Tutorial"
Level 5

Title "ring_nf"

Introduction "This level introduces a new tactic called ring_nf.
This will automatically reduce a complicated equation to its simplest form.
Try it out by typing ring_nf."

Statement (a b : Nat) (h : b * 8 + a = 60) : (3 * b + (a + 5 * b) = 60) := by
  ring_nf
  exact h

Conclusion "Alright. You've got some basic tactics. More will be unlocked in later levels.
Your basic algebra section of theorems is all unlocked now. It's worthwhile to spend some time
looking at what you have, so you know what tools you'll have available to solve levels.
Now... it's time for even/odd world!"

/-- Simplifies equations. Very useful. --/
TacticDoc ring_nf
NewTactic ring_nf

/-- a * b = b * a -/
TheoremDoc Nat.mul_comm as "Nat.mul_comm" in "Basic Arithmetic"
/-- a * b * c = a * (b * c) -/
TheoremDoc Nat.mul_assoc as "Nat.mul_assoc" in "Basic Arithmetic"
/-- (a - b) * c = a * c - b * c -/
TheoremDoc Nat.mul_sub_right_distrib as "Nat.mul_sub_right_distrib" in "Basic Arithmetic"
  /-- a * (b - c) = a * b - a * c -/
TheoremDoc Nat.mul_sub_left_distrib as "Nat.mul_sub_left_distrib" in "Basic Arithmetic"
/-- a * 1 = a -/
TheoremDoc mul_one as "mul_one" in "Basic Arithmetic"
/-- a ^ 2 = a * a -/
TheoremDoc pow_two as "pow_two" in "Basic Arithmetic"
/-- a ^ 3 = a * (a * a) -/
TheoremDoc pow_three as "pow_three" in "Basic Arithmetic"
/-- a - b - c = a - (b + c) -/
TheoremDoc Nat.sub_sub as "Nat.sub_sub" in "Basic Arithmetic"
  /-- a + b - b = a -/
TheoremDoc Nat.add_sub_cancel as "Nat.add_sub_cancel" in "Basic Arithmetic"

NewTheorem Nat.mul_comm Nat.mul_assoc Nat.mul_sub_right_distrib Nat.mul_sub_left_distrib mul_one
pow_two pow_three Nat.sub_sub Nat.add_sub_cancel
