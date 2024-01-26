import Game.Metadata
import Game.Levels.ThreevenThrodd.L09_thre_thro_or_thru
import Mathlib.Tactic

World "ThreevenThrodd"
Level 10

Title "Threeven World Boss"

/-- A number is theeven, throver, or thrunder --/
TheoremDoc thre_thro_or_thru as "thre_thro_or_thru" in "Threeven/Throdd"


Introduction "It's time to fight the final boss! Good luck!"

Statement (n : Nat) : (threeven (n^3 - n)) := by
  cases' thre_thro_or_thru n with h1 h2
  {
    apply sub_threevens
    {
      rw [pow_three]
      apply mul_threevens
      {
        exact h1
      }
      {
        exact mul_threevens n n h1 h1
      }
    }
    {
      exact h1
    }
  }
  {
    rw [pow_three]
    cases' h2 with h3 h4
    {
      apply sub_throvers
      {
        apply mul_throvers
        {
          exact h3
        }
        {
          exact mul_throvers n n h3 h3
        }
      }
      {
        exact h3
      }
    }
    {
      apply sub_thrunders
      {
        apply mul_thrunder_throver
        {
          exact h4
        }
        {
          exact mul_thrunders n n h4 h4
        }
      }
      {
        exact h4
      }
    }
  }

Conclusion "Congratulations! You completed the Threeven Game!"
