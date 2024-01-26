import Game.Metadata
import Game.Levels.EvenOdd.L02_one_odd

World "EvenOdd"
Level 3

Title "Adding even numbers"

/-- An even number plus an even number is an even number. -/
TheoremDoc add_evens as "add_evens" in "Odd/Even"


Introduction "This is where it starts to get tricky. We need a new tactic to solve this level.
This tactic is called cases'. (Don't forget the apostrophe!)
Cases' has many uses, which you can see in the tactic's documentation.
In this level, we are going to use cases to replace even with its definition.
Try typing ''cases' h1 with n hn''. You should see assumption h1 dissapear and be replaced
by a new assumption hn and a natural number n. Can you solve the level from here?
(Hint: you can input a hypothesis into rw to rewrite your goal based on that hypothesis,
sort of like substituting a variable.)"

Statement add_evens (a b : Nat) (h1 : even a) (h2 : even b) : even (a + b) := by
  cases' h1 with n hn
  cases' h2 with m hm
  rw [hn, hm]
  use (n + m)
  rw [Nat.mul_add]

Conclusion "Awesome job! Take a look at my solution:

cases' h1 with n hn

cases' h2 with m hm

rw [hn, hm]

use (n + m)

rw [Nat.mul_add]"

/-- More documentation coming soon! -/

TacticDoc cases'

NewTactic cases'
