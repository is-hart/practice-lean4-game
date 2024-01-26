import Game.Metadata
import Game.Levels.EvenOdd.L08_sub_odd
import Mathlib.Tactic

World "EvenOdd"
Level 9

Title "Every number is even or odd"

/-- A number is either even or odd. -/
TheoremDoc even_or_odd as "even_or_odd" in "Even/Odd"

Introduction "Time for a new tactic, and a new use of an old tactic!
Let's start with the new use for cases'. If you have an or statement in an assumption,
you can use this to handle each side of the or seperately, in a seperate hypothesis.
You write ''cases h1 with h2 h3'', where h1 is the assumption with an or, and
h2 and h3 are the names of the new assumptions that will be created.
It's nice to use curly brackets to separate the two assumptions created.
Not necsessary, just visually nicer.
Remember that we can still use cases' like we did in the last 6 levels.


Our new tactic is induction' (again, it has an annoying apostrophe).
induction' can be used to split a goal into multiple parts.
You write ''induction' n with d hd'', where n is a nat, and d and hd are names of objects/assumptions
that will be created. This will split your goal into two goals,
one for each of the cases of a natural number. This, as mentioned before, is 0 and succ ℕ.
In the second case you are provided with an ''inductive hypothesis''.
This is what you want to prove, and you need to rewrite your goal to match it.


I'll give you the first line of the proof to get you started:

induction' a with d hd"

Statement even_or_odd (a : Nat) : (even a) ∨ (odd a) := by
  induction' a with d hd
  {
    left
    exact zero_even
  }
  {
    cases' hd with h1 h2
    {
      right
      cases' h1 with q h3
      rw [h3]
      use q
    }
    {
      left
      cases' h2 with q2 h4
      rw [h4]
      use (q2 + 1)
      rw [mul_add]
    }
  }

Conclusion "Amazing job! Now all that stands between you and this game's namesake is
the final boss of this world.

I'll give you my solution for this level so you can compare with yours:

Statement even_or_odd (a : Nat) : (even a) ∨ (odd a) := by

  induction' a with d hd

  {

    left

    exact zero_even

  }

  {

    cases' hd with h1 h2

    {

      right

      cases' h1 with q h3

      rw [h3]

      use q

    }

    {

      left

      cases' h2 with q2 h4

      rw [h4]

      use (q2 + 1)

      rw [mul_add]

    }

  }"

/-- More documentation coming soon! -/
TacticDoc induction'
NewTactic induction'
