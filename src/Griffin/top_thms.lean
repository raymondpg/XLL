import tactic
import topology.basic
import topology.subset_properties
/-
Prove connectedness theorems in topology, basic goal to aim for is that if connected spaces share a point, the union is connected. More advanced is goal is closed intervals of the real line are connected.
-/

--use top theorems
open set function topological_space relation
open_locale classical topological_space

-- some vars we can work with
universes u v
variables {α : Type u} [topological_space α] {s t u v : set α}

/- definition of connectivity we use (from mathlibs def of is_preconnected),-/
def connected (s : set α) : Prop :=
∀ (u v : set α), is_open u → is_open v → s ⊆ u ∪ v → (s ∩ u).nonempty → (s ∩ v).nonempty → (s ∩ (u ∩ v)).nonempty

--a theorem I found from other sources to be a nice precursor for other connectivity theorems.
-- if for each point in a set, we can find a connected set contain both that point and a given fixed point (x), then the whole set must be connected.
--Most of the proof as I wrote it is unwrapping definitions
theorem fixedpoint_connected_is_connected {s : set α} (x : α)
  (H : ∀ y ∈ s, ∃ t ⊆ s, x ∈ t ∧ y ∈ t ∧ connected t) :
  connected s :=
begin
 -- Decompose hypothesis to extract sets we can work with
  intros u v hu hv hs hy hz,
  cases hy with y hy,
  cases hy with ys yv,
  cases hz with z hz,
  cases hz with zs zv,
  have xs : x ∈ s, {
    cases H y ys with t h,
    cases h with ts h,
    cases h with xt h,
    cases h with yt con_t,
    exact ts xt,
  },
  --wlog gets around the fact that we would otherwise have to do cases on u,v, but they are identical.
  wlog xu : x ∈ u := hs xs using [u v z y, v u y z],
  specialize H z zs,
  rcases H with ⟨t, ts, xt, zt, ht⟩,
  --use connectivity of t to finish
  specialize ht u v,
  specialize ht hu hv,
  specialize ht (subset.trans ts hs),
  -- x proves t ∩ u nonempty, z proves t ∩ v nonempty
  have h1 : x ∈ t ∩ u, {
  split,
  exact xt,
  exact xu,
  },
  have h2 : (t ∩ u).nonempty, {
    use x,
    exact h1,
  },
   specialize ht h2,
  have h3 : z ∈ t ∩ v, {
    split,
    exact zt,
    exact zv,
  },
  have h4 : (t ∩ v).nonempty, {
    use z,
    exact h3,
  },
  specialize ht h4,
  cases ht with e ht_e,
  cases ht_e with et euv,
  use e,
  split,
  exact ts et,
  exact euv,
end