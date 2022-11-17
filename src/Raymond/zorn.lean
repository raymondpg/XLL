import tactic
import ring_theory.ideal.basic

open set

variables {A: Type} [comm_ring A] (S: ideal A)

#check (univ: set (ideal A))


-- def powerset (B : set A) : set (set A) := {C : set A | C ⊆ B}

def is_proper := {S : ideal A| ((1:A) ∉ S)}
def all_ideals := set(ideal A)


def zero_is_ideal : ideal A :=
{ carrier := {(0: A)},
  zero_mem' := 
  begin
    simp,
  end,
  add_mem' :=
  begin
    intros a b ha hb,
    have ha_rw: a = 0, {
      cases ha,
      refl,
    },
    have hb_rw: b = 0, {
      cases hb,
      refl,
    },
    rw ha_rw,
    rw hb_rw,
    ring_nf,
    simp,
  end,
  smul_mem' :=
  begin
    intros c x hx,
    have rw_hx: x = 0, {
      use hx,
    },
    rw rw_hx,
    simp,
  end,
}

def set_to_ideal (eles: set A) (zero_mem : (0 : A) ∈ eles)
    (add_mem: ∀ (a b : A), a ∈ eles → b ∈ eles → a + b ∈ eles)
    (smul_mem: ∀ (c x: A), x ∈ eles → c • x ∈ eles): ideal A :=
{
  carrier := eles,
  zero_mem' := zero_mem,
  add_mem' := add_mem,
  smul_mem' := smul_mem,
}

