import Mathlib.Tactic

namespace threeven

def threeven (a : Nat) := ∃ n : Nat, a = 3 * n
def thrunder (a : Nat) := ∃ n : Nat, a = 3 * n + 1
def throver (a : Nat) := ∃ n : Nat, a = 3 * n + 2

theorem threeven_times_threeven (a b : Nat) (h1 : threeven a) (h2 : threeven b) : (threeven (a * b)) := by
  cases' h1 with c h3
  cases' h2 with d h4
  rw [h3, h4, mul_assoc, mul_comm c]
  use (3 * d * c)

theorem thrunder_times_thrunder (a b : Nat) (h1 : thrunder a) (h2 : thrunder b) : (thrunder (a * b)) := by
  cases' h1 with c h3
  cases' h2 with d h4
  rw [h3, h4]
  ring_nf
  use (c + d + (c * d * 3))
  ring_nf

theorem throver_times_throver (a b : Nat) (h1 : throver a) (h2 : throver b) : (thrunder (a * b)) := by
  cases' h1 with c h3
  cases' h2 with d h4
  rw [h3, h4]
  ring_nf
  use (c * 2 + d * 2 + c * d * 3 + 1)
  ring_nf

theorem throver_times_thrunder (a b : Nat) (h1 : throver a) (h2 : thrunder b) : (throver (a * b)) := by
  sorry

theorem threeven_sub_threeven (a b : Nat) (h1 : threeven a) (h2 : threeven b) : (threeven (a - b)) := by
  cases' h1 with c h3
  cases' h2 with d h4
  rw [h3, h4]
  use (c - d)
  ring_nf
  rw [Nat.mul_sub_right_distrib c d 3]

theorem thrunder_sub_thrunder (a b : Nat) (h1 : thrunder a) (h2 : thrunder b) : (threeven (a - b)) := by
  cases' h1 with c h3
  cases' h2 with d h4
  rw [h3, h4]
  ring_nf
  use c - d
  rw [← sub_sub (1 + c * 3) 1 (d * 3)]

theorem throver_sub_throver (a b : Nat) (h1 : throver a) (h2 : throver b) : (threeven (a - b)) := by
  sorry

theorem thre_thru_or_thro (a : Nat) : (threeven a) ∨ (thrunder a) ∨ (throver a) := by
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
          rw [hs, ← Nat.add_one, add_assoc, ← mul_one (2 + 1), ← mul_add]
          use (s + 1)
        }
      }
    }
  }

theorem cube_n_minus_n_is_threeven (n : Nat) : (threeven (n^3 - n)) := by
  cases' thre_thru_or_thro n with h1 h2
  {
    apply threeven_sub_threeven
    {
      rw [pow_three]
      apply threeven_times_threeven
      {
        exact h1
      }
      {
        exact threeven_times_threeven n n h1 h1
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
      apply thrunder_sub_thrunder
      {
        apply thrunder_times_thrunder
        {
          exact h3
        }
        {
          exact thrunder_times_thrunder n n h3 h3
        }
      }
      {
        exact h3
      }
    }
    {
      apply throver_sub_throver
      {
        apply throver_times_thrunder
        {
          exact h4
        }
        {
          exact throver_times_throver n n h4 h4
        }
      }
      {
        exact h4
      }
    }
  }
