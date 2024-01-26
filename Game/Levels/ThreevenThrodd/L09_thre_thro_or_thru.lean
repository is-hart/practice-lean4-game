import Game.Metadata
import Game.Levels.ThreevenThrodd.L08_sub_thrunder
import Mathlib.Tactic

World "ThreevenThrodd"
Level 9

Title "Threeven, Throver, or Thrunder"

/-- A number is theeven, throver, or thrunder --/
TheoremDoc thre_thro_or_thru as "thre_thro_or_thru" in "Threeven/Throdd"


Introduction "You need induction for this mini-boss.

If you want to rewrite a specific part of an equation, provide one or more natural numbers
after the theorem name. It will take the nat(s) as inputs.
You will need this to solve this problem."

Statement thre_thro_or_thru (a : Nat) : (threeven a) ∨ (throver a) ∨ (thrunder a) := by
  induction' a with d hd
  {
    left
    use 0
  }
  {
    cases' hd with h1 h2
    {
      right
      left
      cases' h1 with q hq
      rw [hq]
      use q
    }
    {
      cases' h2 with h3 h4
      {
        right
        right
        cases' h3 with r hr
        rw [hr]
        use r
      }
      {
        left
        cases' h4 with s hs
        {
          rw [hs, ← Nat.add_one, Nat.add_assoc, ← mul_one (2 + 1), ← Nat.mul_add]
          use (s + 1)
        }
      }
    }
  }

Conclusion "Great job!

You may want to take a look at my solution:
{
  induction' a with d hd
  {
    left
    use 0
  }
  {
    cases' hd with h1 h2
    {
      right
      left
      cases' h1 with q hq
      rw [hq]
      use q
    }
    {
      cases' h2 with h3 h4
      {
        right
        right
        cases' h3 with r hr
        rw [hr]
        use r
      }
      {
        left
        cases' h4 with s hs
        {
          rw [hs, ← Nat.add_one, Nat.add_assoc, ← mul_one (2 + 1), ← Nat.mul_add]
          use (s + 1)
        }
      }
    }
  }
}"
