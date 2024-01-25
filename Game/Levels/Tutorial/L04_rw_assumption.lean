import Game.Metadata
import Game.Levels.Tutorial.L03_rw_backwards

World "Tutorial"
Level 4

Title "Rewriting Assumptions"

Introduction "We're going to practice using rw on our assumption this time rather than our goal.
Type rw [theorem] at hypothesis
Note that you could also use rw on your goal to solve this, but that wouldn't teach you much, would it?
This time we'll introduce the associative property of multiplication.
This is split into two theorems, one called Nat.mul_add, for left distributivity, and Nat.add_mul for right distributivity.
If you get mixed up, remember you can always check your inventory of theorems for more info on each of them.
"

/-- practice --/
TheoremDoc practice4 as "practice4" in "Don't Use These"

Statement practice4 (a b c : Nat) (h : a * (b + c) = 123) : (a * b + a * c = 123) := by
  rw [Nat.mul_add] at h
  exact h

Conclusion "Great."

/-- a * (b + c) = a * b + a * c --/
TheoremDoc Nat.mul_add as "Nat.mul_add" in "Basic Arithmetic"

/-- (a + b) * c = a * c + b * c --/
TheoremDoc Nat.add_mul as "Nat.add_mul" in "Basic Arithmetic"

NewTheorem Nat.mul_add Nat.add_mul
