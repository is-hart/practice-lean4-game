import Game.Metadata
import Game.Levels.EvenOdd.L02_one_odd

World "EvenOdd"
Level 3

Title "Adding even numbers"

/-- An even number plus an even number is an even number. -/
TheoremDoc add_evens as "add_evens" in "Even/Odd"


Introduction "This is where it starts to get tricky. We need a new tactic to solve this level.
This tactic is called cases'. (Don't forget the apostrophe!)
Cases' has many uses, which you can see in the tactic's documentation.
In this level, we are going to use cases to replace even with its definition.
Try typing {cases' h1 with n hn}. You should see assumption h1 dissapear and be replaced
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
{
cases' h1 with n hn
cases' h2 with m hm
rw [hn, hm]
use (n + m)
rw [Nat.mul_add]
}"

/-- Some examples of cases' in action:
If h : P ∨ Q is a hypothesis, then {cases' h with hp hq} will turn one goal into two goals,
one with a hypothesis hp : P and the other with a hypothesis hq : Q.

If h : even(a) is a hypothesis, then {cases' h with b hb} will create a new number b and a proof
hb : a = b * 2. This is because the definition of even(a) is {∃ b, a = b * 2}.-/

TacticDoc cases'

NewTactic cases'
