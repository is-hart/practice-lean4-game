import Game.Metadata
import Game.Levels.EvenOdd.L09_even_or_odd
import Mathlib.Tactic

World "EvenOdd"
Level 10

Title "Even World Boss"

Introduction "The boss approaches slowly. It seems you have just enough time to learn one last
tactic before it reaches you.

All of the even/odd theorems you've proved are implication theorems.
This means one thing implies another. You can't use rewrite to use these theorems.
This is where apply comes in. Write apply theoremName to use it.

Apply is smart. Even if you think you don't have enough info to use it,
it may help.

I'd tell you more, but the boss has reached us.
I think I'll take my leave before I can get caught up in the fray.
Good luck, and see you in threeven world!"

Statement (n : Nat) : (even (n^2 - n)) := by
  cases' even_or_odd n with h1 h2
  {
    rw [pow_two]
    apply sub_evens
    {
      exact mul_evens n n h1 h1
    }
    {
      exact h1
    }
  }
  {
    rw [pow_two]
    apply sub_odds
    {
      exact mul_odds n n h2 h2
    }
    {
      exact h2
    }
  }

Conclusion "You did it! It wasn't that hard now, was it?
Sadly, what you just proved isn't too useful to us, but it made a fun excercise, didn't it?"

/-- Apply will use an implication theorem on a statement.
If you don't have quite the right structure to use it, don't worry.
It will split up your goal into smaller chunks for you to prove individually. -/
TacticDoc apply
NewTactic apply
