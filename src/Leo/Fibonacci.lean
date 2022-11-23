--proving random stuff about fibonacci numbers
--hopefully show F_n | F_m if n | m
import tactic

--useful for working with Sigma notation
open_locale big_operators
open finset

def F : ℕ → ℤ
| 0 := 0
| 1 := 1
| (n + 2) := F n + F (n + 1)

lemma fib_nonneg' (n : ℕ) : ∀ m ≤ n, F m ≥ 0 :=
begin
  cases n,
  { intros,
    cases H,
    exact le_refl _,
  },
  induction n with n hn,
  { intros,
    cases H with H1 H2,
    { exact int.one_nonneg},
    { change m ≤ 0 at H2,
      rw nat.le_zero_iff at H2,
      rw H2,
      exact le_refl _,},
  },
  { intros,
    cases H with H1 H2,
    { change F n + F (n + 1) ≥ 0,
      apply add_nonneg,
      { apply hn,
        exact nat.le_succ n,
      },
      { apply hn,
        exact le_refl _,
      }
    },
    { exact hn m H2,}
  },
end
lemma fib_nonneg (n : ℕ) : F n ≥ 0 := fib_nonneg' n n (le_refl n)
lemma fib_add_two (n : ℕ) : F (n + 2) = F n + F (n + 1) := rfl
@[simp] lemma fib_zero : F 0 = 0 := rfl
@[simp] lemma fib_one : F 1 = 1 := rfl
@[simp] lemma fib_two : F 2 = 1 := rfl

example (n : ℕ) : ∑ i in range n, F i = F (n + 1) - 1 :=
begin
  induction n with n hn,
  { simp [F],},
  { rw sum_range_succ,
    rw hn,
    rw fib_add_two,
    ring,
  }
end

example (n : ℕ) : ∑ i in range (n + 1), (F i)^2 = F (n) * F (n+1) :=
begin
  induction n with n ih,
  { refl,},
  { rw sum_range_succ,
    rw ih,
    rw fib_add_two,
    ring,
  }
end

lemma fibonacci_hell' (m n : ℕ) : ∀ k : ℕ, k ≤ n → F (m + k + 1) = 
  F (m + 1) * F (k + 1) + F m * F k :=
begin
  cases n,
  {simp,},
  induction n with n ih,
  { rintro ⟨k, rfl⟩,
    simp,
    intro h,
    cases h with h h,
    rw fib_add_two,
    simp,
    rw add_comm,
    cases h,
  },
  { intros k hk,
    cases hk with hk hk,
    { rw nat.add_succ m,
      rw fib_add_two,
      nth_rewrite 0 nat.add_succ,
      rw ih n (nat.le_succ n),
      rw ih (n.succ) (le_refl n.succ),
      rw fib_add_two n.succ,
      rw fib_add_two,
      ring,
    },
    { exact ih k hk},
  }
end

lemma fibonacci_hell (m n : ℕ) : F (m + n + 1) = 
  F (m + 1) * F (n + 1) + F m * F n := fibonacci_hell' m n n (le_refl n)

lemma fib_dvd_fib (m n : ℕ) : n ∣ m → F n ∣ F m :=
begin
  rintro ⟨k, rfl⟩,
  cases n,
  { simp},
  induction k with k ih,
  { simp,},
  { have H : n.succ * k.succ = n.succ + n.succ*k := by {zify, ring},
    rw H,
    have H2 := fibonacci_hell n.succ (n.succ*k - 1),
    cases k,
    { simp,},
    have H3 : n.succ * k.succ - 1 + 1 = n.succ * k.succ,
      { apply nat.succ_pred_eq_of_pos,
        apply mul_pos;
        apply nat.succ_pos,
      },
    rw add_assoc at H2,
    rw H3 at H2,
    rw H2,
    apply dvd_add,
    { exact dvd_mul_of_dvd_right ih (F (nat.succ n + 1)),},
    { apply dvd_mul_right,},
  }
end