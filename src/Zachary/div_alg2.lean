import tactic                 
import data.nat.lattice       -- for well-ordering for naturals 
import data.set.basic         -- for creating sets

-- Define a set for the remainder of a/b :
-- remainder_set takes a and b and returns set of all possible nonnegative remainders of a/b

def remainder_set : ℤ → ℤ → set ℕ := λ a, λ b, { y | ∃ x : ℤ, (y : ℤ) = a - b * x}

-- lemma using the definition of remainder_set (to make it easier to work with)
--
lemma mem_remainder_set_iff {a b : ℤ} {k : ℕ}  : (k ∈ remainder_set a b) ↔
  ∃ x : ℤ, (k : ℤ) = a - b * x :=
  begin
    split, {
      intro h,
      rw set.mem_def at h,
      exact h,
    }, {
      intro h,
      rw set.mem_def,
      exact h,
    }
  end

/-       PROOF SKETCH

  (1) Define remainder set, S
      -- let S = {a - bx : x ∈ ℤ ∧ a - bx ≥ 0}

  (2) Show S is nonempty
      -- use x = -|a|, and a + b |a| ≥ 0 to show S nonempty

  (3) Apply Well-ordering of naturals to show that S contains a minimum, r

  (4) Show r satisfies conditions of division algorithm
      -- show r < b, by contradiction if r - b ≥ 0 

  (5) Show uniqueness 

-/

lemma pos_z_pos_nat { b : ℤ } (hb : b > 0 ) : (b.to_nat > 0) :=
begin
  have hb2 := (le_of_lt hb),
  rw ← (int.to_nat_of_nonneg hb2) at hb,
  exact int.coe_nat_pos.mp hb,
end

lemma division_algorithm (a b : ℤ) (ha : a > 0) (hb : b > 0) : 
(∃ q r : ℤ, ((a = b * q + r) ∧ (0 ≤ r) ∧ (r < b))) :=
begin
  -- (1) Define remainder set, S
  --     let S = {a - bx : x ∈ ℤ ∧ a - bx ≥ 0}
  set S := remainder_set a b,
  set r := has_Inf.Inf S,

  -- (2) Show S is nonempty
  --     use x = -|a|, and a + b |a| ≥ 0 to show S nonempty
  have hns : S.nonempty,
  {
    have h1 : a + b * |a| ≥ 0,
      { 
        rw abs_of_pos ha,
        exact le_of_lt (add_pos ha (mul_pos hb ha)),
      },
    obtain ⟨k, hk⟩ := int.eq_coe_of_zero_le (h1),
    have hk_mem : k ∈ S,
      {
        rw mem_remainder_set_iff,
        use (-|a|),
        linarith,
      },
    exact set.nonempty_of_mem hk_mem,
  },

  -- (3) Apply Well-ordering of naturals to show that S contains a minimum, r
  have hr : r ∈ S := Inf_mem hns,

  -- (4) Show r satisfies conditions of division algorithm
  --     show r < b, by contradiction: if r - b ≥ 0, then r - b ∈ S, so r - b ≤ r since r = Inf S.
  rw mem_remainder_set_iff at hr,
  cases hr with x hx,
  use [x, r],

  have hb_coe_coe := int.to_nat_of_nonneg (le_of_lt hb),
  
  split, {
    rw [hx, add_sub_cancel'_right],
  }, {
    split, {
      exact int.of_nat_nonneg r,
    }, {
      by_contra, 
      push_neg at h,
      rw ← hb_coe_coe at h,

      have hc : (r - b.to_nat) ∈ S,
      { 
        rw mem_remainder_set_iff,
        use ( x + 1 ),
        rw [int.coe_nat_sub (int.coe_nat_le.mp h), hx, hb_coe_coe],
        linarith,
      },
      have hg : r - b.to_nat < r := (b.to_nat).sub_lt_of_pos_le r (pos_z_pos_nat hb) (int.coe_nat_le.mp h),
      exact nat.lt_le_antisymm hg (nat.Inf_le hc),
    },
  },
end
 
#print division_algorithm -- theorem above is one big λ function!

-- (5) Show uniqueness 

lemma division_algorithm_uniqueness (a b q1 q2 r1 r2 : ℤ) (hr1 : (0 ≤ r1) ∧ (r1 < b)) (hr2 : (0 ≤ r2) ∧ (r2 < b)) 
(ha : a > 0) (hb : b > 0) (hd1 : a = b * q1 + r1) (hd2 : a = b * q2 + r2) : (q1 = q2 ∧ r1 = r2) :=
begin
    have hq : q1 = q2,
    { 
      rw hd2 at hd1,
      have j : b * (q2 - q1) = r1 - r2 := by linarith,

      have k : -b < -r2 ∧ -r2 ≤ 0,
      { split, { linarith, }, { linarith, },},

      have l : -b < r1 - r2 ∧ r1 - r2 < b,
      { split, { linarith,}, { linarith,},},

      have m : -b < b*(q2 - q1) ∧ b*(q2 - q1) < b,
      { split, {linarith,}, {linarith,},},

      have i : -1 < q2 - q1 ∧ q2 - q1 < 1,
      {split, {
        cases m,
        rw (show -b = b*(-1), by linarith) at m_left,
        exact (mul_lt_mul_left hb).mp m_left,
      }, {
        cases m,
        nth_rewrite 1 ← (mul_one b) at m_right,
        exact (mul_lt_mul_left hb).mp m_right,
      },},
      linarith,
  
    },
    split, {
      assumption,
    }, {
      rw hq at hd1,
      linarith,
    },
end

-- how would you use the division algorithm from the library?
-- use ℤ is an instance of Euclidean Domain

theorem division_algorithm' (a b : ℤ) (ha : a > 0) (hb : b > 0) : 
(∃ q r : ℤ, ((a = b * q + r) ∧ (0 ≤ r) ∧ (r < b))) :=
begin
  have h := euclidean_domain.mod_add_div a b,  -- q, r not unique for general ED 
  use [(a/b), a % b ], -- q = a/b ; r = a % b
  exact ⟨(euclidean_domain.quotient_mul_add_remainder_eq a b).symm, int.mod_nonneg a (ne_of_gt hb), int.mod_lt_of_pos a hb,⟩,
end

