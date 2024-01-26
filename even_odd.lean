import Mathlib.Tactic

namespace practice

def even (a : Nat) := ∃ n : Nat, a = 2 * n
def odd (a : Nat) := ∃ n : Nat, a = 2 * n + 1

theorem even_zero : even 0 := by
  use 0

theorem not_odd_zero : ¬ odd 0 := by
  sorry

theorem even_four : even 4 := by
  use 2

theorem odd_one : odd 1 := by
  use 0

theorem even_plus_even_is_even (a b : Nat) (h1 : even a) (h2 : even b) : even (a + b) := by
  cases' h1 with n hn
  cases' h2 with m hm
  rw [hn, hm]
  rw [← mul_add]
  use (n + m)

theorem odd_plus_even_is_odd (a b : Nat) (h1 : odd a) (h2 : even b) : odd (a + b) := by
  cases' h1 with n hn
  cases' h2 with m hm
  rw [hn, hm]
  use (n + m)
  ring_nf

theorem even_plus_odd_is_odd (a b : Nat) (h1 : even a) (h2 : odd b) : odd (a + b) := by
  rw [add_comm]
  apply odd_plus_even_is_odd
  exact h2
  exact h1

theorem odd_plus_odd_is_even (a b : Nat) (h1 : odd a) (h2 : odd b) : even (a + b) := by
  cases' h1 with n hn
  cases' h2 with m hm
  rw [hn, hm]
  use (n + m + 1)
  ring_nf

theorem even_times_even_is_even (a b : Nat) (h1 : even a) (h2 : even b) : even (a * b) := by
  cases' h1 with n hn
  cases' h2 with m hm
  rw [hn, hm]
  use (n * m * 2)
  ring_nf

theorem odd_times_odd_is_odd (a b : Nat) (h1 : odd a) (h2 : odd b) : odd (a * b) := by
  cases' h1 with n hn
  cases' h2 with m hm
  rw [hn, hm]
  use (n + m + n * m * 2)
  ring_nf

theorem even_or_odd (a : Nat) : (even a) ∨ (odd a) := by
  induction' a with d hd
  {
    left
    exact even_zero
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

theorem even_sub_even (h1 : even a) (h2 : even b) : even (a - b) := by
  cases' h1 with n hn
  cases' h2 with m hm
  rw [hn, hm, ← Nat.mul_sub_left_distrib]
  use (n - m)

theorem odd_sub_odd (h1 : odd a) (h2 : odd b) : even (a - b) := by
  sorry

theorem even_n_sq_minus_n (n : Nat) : (even (n^2 - n)) := by
  cases' even_or_odd n with h1 h2
  {
    rw [pow_two]
    apply even_sub_even
    {
      exact even_times_even_is_even n n h1 h1
    }
    {
      exact h1
    }
  }
  {
    rw [pow_two]
    apply odd_sub_odd
    {
      exact odd_times_odd_is_odd n n h2 h2
    }
    {
      exact h2
    }
  }




def zeromod2 : Nat → Bool
  | Nat.zero => true
  | x + 1 => not (zeromod2 x)

def onemod2 : Nat → Bool
  | Nat.zero => false
  | x + 1 => not (zeromod2 x)
