import Game.Metadata
import Game.Levels.EvenOdd.L07_sub_even
import Mathlib.Tactic

World "EvenOdd"
Level 8

Title "Multiplying odd numbers"

/-- An odd number minus an odd number is even. -/
TheoremDoc sub_odds as "sub_odds" in "Even/Odd"

Introduction "This may seem like all the other levels, but in truth it requires some tricky
rewriting using some arithmetic theorems we haven't used yet."
Statement sub_odds (a b : Nat) (h1 : odd a) (h2 : odd b) : even (a - b) := by
  cases' h1 with n hn
  cases' h2 with m hm
  rw [hn, hm]
  use (n - m)
  ring_nf
  rw [← Nat.sub_sub]
  rw [add_comm, Nat.add_sub_cancel, Nat.mul_sub_right_distrib]

Conclusion "Alright, now you're ready for the sub-boss of this world,
and once you beat it you can challenge the big boss!"
