
import analysis.calculus.local_extr
import analysis.convex.slope
import analysis.convex.topology
import data.complex.is_R_or_C
import data.real.basic
import tactic.suggest
import tuto_lib
import data.nat.modeq
import tactic

-- whnf, weak head normal form
--
-- normal form
-- 1 + 2 is not normal form, since it can be evaluated to 3, thus
-- the normal form is 3 since there is nothing to be further evaluated
-- 
-- weak head normal form only evaluates the outermost structure,
-- sub-expressions may not have been evaluated
-- 
-- (Haskell example) (1 + 1, 2 + 2) is in whnf since the outermost
-- expression, the data constructor (,) cannot be further evaluated
-- 
-- https://stackoverflow.com/questions/6872898/what-is-weak-head-normal-form

example (a b c d : ℕ) : (a * d) * (b * c) = (d * a) * (c * b) :=
begin
  -- solutions to a = (b * c) = a * (c * b)

  -- rw mul_comm,             -- unhelpful, it doesn't rewrite what we want it to
  
  -- rw mul_comm b c,

  -- nth_rewrite 1 mul_comm,  -- another useful tactic

  -- solution to (a * d) * (b * c) = (d * a) * (c * b)

  conv
  begin                       -- | (a * d) * (b * c) = a * (c * b)
    to_lhs,                   -- | (a * d) * (b * c)
    congr,                    -- 2 goals : | a * d and | b * c
    rw mul_comm,              -- | d * a
    skip,                     -- | b * c
    rw mul_comm,              -- | c * b
  end,                        -- ⊢ (d * a) * (c * b) = (d * a) * (c * b)
end

example : (λ x : ℕ, 0 + x) = (λ x, x) :=
begin
  -- rw zero_add, -- unhelpful, can't get past λ binder
  
  -- by funext;
  -- rw zero_add,

  conv
  begin           -- | (λ (x : ℕ), 0 + x) = λ (x : ℕ), x
    to_lhs,       -- | λ (x : ℕ), 0 + x
    funext,       -- | 0 + x
    rw zero_add,  -- | x
  end
end

-- "Beware that a well known bug makes Lean printing: "find converter failed, pattern was not found"
-- when the tactics inside conversion mode fail, even if the pattern was actually found."
example (a b c : ℕ) : a * (b * c) = a * (c * b) :=
begin
  conv in (b*c)  -- finds the first match to the pattern
  begin          -- | b * c
    rw mul_comm, -- | c * b
  end
end

-- one liner
example (a b c : ℕ) : a * (b * c) = a * (c * b) :=
by conv in (b*c) { rw mul_comm }

-- wildcard
example (a b c : ℕ) : a + (b * c) = a + (c * b) :=
by conv in (_ * c) { rw mul_comm }

-- mul_comm on only 2nd and 3rd (b * c)
example (a b c : ℕ) : (b * c) * (b * c) * (b * c) = (b * c) * (c * b)  * (c * b):=
by conv { for (b * c) [2, 3] { rw mul_comm } }

---------------------------------------------------------



-- contrapose + push_neg = contrapose!

example (x y : ℝ) : x < y → y > x :=
begin
  -- contrapose,     -- take the contrapositive
  -- push_neg,       -- rewrite without negation
  contrapose!,
  simp,
end

-- calculation environment

example (a b c : ℕ) (H1 : a = b + 1) (H2 : b = c) : a = c + 1 :=
calc a = b + 1 : H1
...    = c + 1 : by rw H2

example (a b c : ℕ) (H1 : a = b + 1) (H2 : b = c) : a = c + 1 :=
begin
  calc a = b + 1 : H1
  ...    = c + 1 : _,
  { rw H2 }
end

-- Using operators other than equality

definition j : ℕ → ℕ → Prop := sorry
@[trans] theorem j_trans (a b c : ℕ) : j a b → j b c → j a c := sorry
infix `****`: 50 := j     -- left (by default) binding power of 50

example (a b c : ℕ) (H1 : a **** b) (H2 : b **** c) : a **** c :=
calc a **** b : H1
...    **** c : H2

-- Using more than one operator

theorem T2 (a b c d : ℕ)
  (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
begin
calc
  a     = b     : h1
    ... < b + 1 : nat.lt_succ_self b
    ... ≤ c + 1 : nat.succ_le_succ h2
    ... < d     : h3,
end

-- "The way this is done, Kevin thinks (can someone verify this?) is that Lean continually tries to amalgamate
-- the first two operators in the list, until there is only one left."
-- 
-- a = b < b + 1 ≤ c < d
-- a < b + 1 ≤ c + 1 < d
-- a < c + 1 < d
-- a < d

-- Lean recognizes that, given U op1 V and V op2 W, there may be some op3 (which could equal op1 or op2)
-- such that U op3 W
-- "Lean knows:
-- 
-- #check @trans_rel_right -- ∀ {α : Sort u_1} {a b c : α} (r : α → α → Prop), a = b → r b c → r a c
-- #check @trans_rel_left -- ∀ {α : Sort u_1} {a b c : α} (r : α → α → Prop), r a b → b = c → r a c
-- 
-- and (Kevin believes) uses them if one of the operators is an equality operator."
-- If neither are an equality operator, lean searches the database of theorems tagged [trans]
-- and applies them instead, for example

-- @[trans] lemma lt_of_lt_of_le [preorder α] : ∀ {a b c : α}, a < b → b ≤ c → a < c
-- @[trans] lemma lt_trans [preorder α] : ∀ {a b c : α}, a < b → b < c → a < c

-- the combination of two operators can be a new operator
definition r : ℕ → ℕ → Prop := sorry
definition s : ℕ → ℕ → Prop := sorry
definition t : ℕ → ℕ → Prop := sorry
@[trans] theorem rst_trans (a b c : ℕ) : r a b → s b c → t a c := sorry
infix `***`: 50 := r
infix `&&&` : 50 := s
infix `%%%` : 50 := t

example (a b c : ℕ) (H1 : a *** b) (H2 : b &&& c) : a %%% c :=
calc a *** b : H1
...    &&& c : H2

-- https://leanprover-community.github.io/extras/calc.html

--------------------------------------

-- operator precedence parsing:

-- left and right binding power ("infix" and "infixr"), "prefix"

-- "binding power" defines which operations take precedence, similar to PEMDAS
-- left and right binding power define operator associativity. 'a ~ b ~ c' can be interpreted as
-- '(a ~ b) ~ c' or 'a ~ (b ~ c)', left or right binding power respectively determines which way
-- it is interpreted

-- "When 'expression' is called, it is provided the 'rbp' - right binding power of the operator that called it.
-- It consumes tokens until it meets a token whose left binding power is equal or lower than rbp. Specifically,
-- it means that it collects all tokens that bind together before returning it to the operator that called it."

-- negation has a left binding power of 100, i.e. negation of a variable should never be what ends
-- the tokens binding together

-- According to Eli Bendersky's simplified parser example, '(' has a lbp of 0, i.e. it should stop anything

-- https://eli.thegreenplace.net/2010/01/02/top-down-operator-precedence-parsing

-- binding power in lean:

-- https://github.com/leanprover/lean/blob/master/library/init/core.lean

/- Logical operations and relations -/

reserve prefix `¬`:40
reserve prefix `~`:40
reserve infixr ` ∧ `:35
reserve infixr ` /\ `:35
reserve infixr ` \/ `:30
reserve infixr ` ∨ `:30
reserve infix ` <-> `:20
reserve infix ` ↔ `:20
reserve infix ` = `:50
reserve infix ` == `:50
reserve infix ` ≠ `:50
reserve infix ` ≈ `:50
reserve infix ` ~ `:50
reserve infix ` ≡ `:50
reserve infixl ` ⬝ `:75
reserve infixr ` ▸ `:75
reserve infixr ` ▹ `:75

/- types and type constructors -/

reserve infixr ` ⊕ `:30
reserve infixr ` × `:35

/- arithmetic operations -/

reserve infixl ` + `:65
reserve infixl ` - `:65
reserve infixl ` * `:70
reserve infixl ` / `:70
reserve infixl ` % `:70
reserve prefix `-`:100
reserve infixr ` ^ `:80

reserve infixr ` ∘ `:90                 -- input with \comp

reserve infix ` <= `:50
reserve infix ` ≤ `:50
reserve infix ` < `:50
reserve infix ` >= `:50
reserve infix ` ≥ `:50
reserve infix ` > `:50

/- boolean operations -/

reserve infixl ` && `:70
reserve infixl ` || `:65

/- set operations -/

reserve infix ` ∈ `:50
reserve infix ` ∉ `:50
reserve infixl ` ∩ `:70
reserve infixl ` ∪ `:65
reserve infix ` ⊆ `:50
reserve infix ` ⊇ `:50
reserve infix ` ⊂ `:50
reserve infix ` ⊃ `:50
reserve infix ` \ `:70

/- other symbols -/

reserve infix ` ∣ `:50
reserve infixl ` ++ `:65
reserve infixr ` :: `:67
reserve infixl `; `:1

--------------------------------------

-- some simplifications were made to make proving this easier, but perhaps the proof
-- can be modified in order to remove them.
theorem ivt_0 (f : ℝ → ℝ) {a b y : ℝ} (hab : a < b) (hfab : f a < f b) (hfc : continuous_on f (set.Icc a b)) (hy : y ∈ set.Ioo (f a) (f b)):
∃ (c : ℝ) (H : c ∈ set.Ioo a b), f(c) = y :=
begin
  -- define a set S which contains all x in [a, b] such that f(x) < k
  -- let c be the supremum of S
  -- c ≠ a since by continuity of f and with ε = (k - f(a)) / 2 there is
  -- some δ > 0 such that |a - x| < δ |f(x) - f(a)| < ε → f(x) < k, so since
  -- ∃ x > a such that f(x) < k → x ∈ S, then a cannot be the supremum.
  -- b cannot be the supremum for similar reasons, there is a neighborhood around b
  -- where all f(x) are greater than k, so some value less than b must be the supremum.
  -- Now, having c ∈ (a, b), use continuity to show that ∀ ε > 0 we have
  -- k - ε < f(c) < k + ε, since if not then c would not be the supremum of S.
  sorry,
end

-- theorem ivt (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) (hfc : continuous_on f (set.Icc a b))

--------------------------------------

def continuous_at_pt (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - f x₀| ≤ ε

lemma is_sup_iff (A : set ℝ) (x : ℝ) :
(is_sup A x) ↔ (upper_bound A x ∧ ∃ u : ℕ → ℝ, seq_limit u x ∧ ∀ n, u n ∈ A ) :=
begin
  split,
  { intro h,
    split,
    {
      exact h.1,
    },
    { have : ∀ n : ℕ, ∃ a ∈ A, x - 1/(n+1) < a,
      { intros n,
        have : 1/(n+1 : ℝ) > 0,
          exact nat.one_div_pos_of_nat,
        exact lt_sup h _ (by linarith),
      },
      choose u hu using this,
      use u,
      split,
      { apply squeeze (limit_const_sub_inv_succ x) (limit_const x),
        { intros n,
          exact le_of_lt (hu n).2, },
        { intro n,
          exact h.1 _ (hu n).left, } },
      { intro n,
        exact (hu n).left },
  } },
  { rintro ⟨maj, u, limu, u_in⟩, 
    split,
    { exact maj },
    { intros y ymaj,
      apply lim_le limu,
      intro n,
      apply ymaj,
      apply u_in },
  },
end


variables {f : ℝ → ℝ} {x₀ : ℝ} {u : ℕ → ℝ}

lemma seq_continuous_of_continuous (hf : continuous_at_pt f x₀)
  (hu : seq_limit u x₀) : seq_limit (f ∘ u) (f x₀) :=
begin
  intros ε ε_pos,
  unfold continuous_at_pt at hf,
  rcases hf ε ε_pos with ⟨δ, δ_pos, hδ⟩,
  cases hu δ δ_pos with N hN,
  use N,
  intros n hn,
  apply hδ,
  exact hN n hn,
end

lemma stupid {a b x : ℝ} (h : x ∈ set.Icc a b) (h' : x ≠ b) : x < b :=
lt_of_le_of_ne h.right h'

lemma le_lim {x y : ℝ} {u : ℕ → ℝ} (hu : seq_limit u x)
  (ineg : ∃ N, ∀ n ≥ N, y ≤ u n) : y ≤ x :=
begin
  apply le_of_le_add_all,
  intros ε ε_pos,
  cases hu ε ε_pos with N hN,
  cases ineg with N' hN',
  let N₀ := max N N',
  specialize hN N₀ (le_max_left N N'),
  specialize hN' N₀ (le_max_right N N'),
  rw abs_le at hN,
  linarith,
end

theorem ivt (f : ℝ → ℝ) (a b c : ℝ) (hab : a ≤ b) (hf : ∀ (x ∈ set.Icc a b), continuous_at_pt f x) (h₀ : f a < c) (h₁ : f b > c) :
∃ x₀ ∈ set.Icc a b, f x₀ = c :=
begin
  let A := { x | x ∈ set.Icc a b ∧ f x < c},
  have ex_x₀ : ∃ x₀ ∈ set.Icc a b, is_sup A x₀,
  {
    apply sup_segment,
      use a,
      split,
        split, linarith, linarith,
      exact h₀,
    intros x hx,
    exact hx.left
  },
  rcases ex_x₀ with ⟨x₀, x₀_in, x₀_sup⟩,
  use [x₀, x₀_in],
  have : f x₀ ≤ c,
  {
    rw is_sup_iff at x₀_sup,
    rcases x₀_sup with ⟨maj_x₀, u, lim_u, u_dans⟩,
    have : seq_limit (f ∘ u) (f x₀),
      exact seq_continuous_of_continuous (hf x₀ x₀_in) lim_u,
    apply lim_le this,
    intros n,
    have : f (u n) < c,
      exact (u_dans n).right,
    linarith
  },
  have x₀_1: x₀ < b,
  {
    apply stupid x₀_in,
    intro h,
    rw ← h at h₁,
    linarith
  },
  have : f x₀ ≥ c,
  { have in_I : ∃ N : ℕ, ∀ n ≥ N, x₀ + 1/(n+1) ∈ set.Icc a b,
    { have : ∃ N : ℕ, ∀ n≥ N, 1/(n+1 : ℝ) ≤ b-x₀,
      {
        apply inv_succ_le_all,
        linarith,
      },
      cases this with N hN,
      use N,
      intros n hn,
      specialize hN n hn,
      have : 1/(n+1 : ℝ) > 0,
        exact nat.one_div_pos_of_nat,
      change a ≤ x₀ ∧ x₀ ≤ b at x₀_in,
      split ; linarith,
    },
    have not_in : ∀ n : ℕ, x₀ + 1/(n+1) ∉ A,
    {
      intros n hn,
      cases x₀_sup with x₀_maj _,
      specialize x₀_maj _ hn,
      have : 1/(n+1 : ℝ) > 0,
        from nat.one_div_pos_of_nat,
      linarith,
    },
    dsimp [A] at not_in,
    push_neg at not_in,
    have lim : seq_limit (λ n, f(x₀ + 1/(n+1))) (f x₀),
    { apply seq_continuous_of_continuous (hf x₀ x₀_in),
      apply limit_const_add_inv_succ },
    apply le_lim lim,
    cases in_I with N hN,
    use N,
    intros n hn,
    exact not_in n (hN n hn),
  },
  linarith,
end

-- Next Steps: Currently, this proof requires a ≤ b and f a < f b. Can this proof
-- be modified such that it works for a ≥ b and/or f a > f b? How about the trivial
-- case f a = c = f b?