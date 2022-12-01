import tactic -- imports all the Lean tactics
import topology.continuous_function.compact -- continuous functions, compact sets
import topology.constructions
import topology.continuous_on
import topology.category.Top.epi_mono
import topology.path_connected
import data.set.lattice
import data.nat.basic
import topology.subset_properties
import topology.bases
import data.set.basic
import topology.constructions
import topology.separation



variables (X Y : Type) [topological_space X] [topological_space Y]

-- let S be a subset of X
variable (S : set X)

-- Let `f : X → Y` be a function
variables (f : X → Y) 


-- X, Y are path connected space, then their product is path connected
example (h: path_connected_space X) (h1: path_connected_space Y):
  path_connected_space (X × Y) :=
begin
  rw path_connected_space_iff_univ at h h1 ⊢,
  unfold is_path_connected at h1 h ⊢,
  cases h with x hx,
  cases hx with h hx,
  cases h1 with y hy,
  cases hy with h1 hy,
  use (x, y),
  split,
  exact set.mem_univ (x, y),
  intro xy,
  have h2: xy.fst ∈ (set.univ: set X),
  exact set.mem_univ xy.fst,
  specialize hx h2,
  have h3: xy.snd ∈ (set.univ: set Y),
  exact set.mem_univ xy.snd,
  specialize hy h3,
  intro xyuniv,
  have h4: xy = (xy.fst, xy.snd),
  exact prod.ext rfl rfl,
  rw h4,
  unfold joined_in at hx hy ⊢,
  cases hy with p1 hy,
  cases hx with p2 hx,
  
  let p := path.prod p2 p1,
  use p,
  intro interval,
  specialize hx interval,
  specialize hy interval,
  exact set.mem_univ (p interval),
end

-- Show that if U is open in X and A is closed in X, then U − A is open in X, and
-- A − U is closed in X.
example (U : set X) (A : set X): 
  is_open U ∧ is_closed A → is_open (U ∩ Aᶜ) ∧ is_closed (A ∩ Uᶜ) :=
begin
  intro h,cases h with h1 h2,
  split,
  {
    have claim: is_open Aᶜ,
    exact is_open_compl_iff.mpr h2,
    exact is_open.inter h1 claim,
  },
  {
    have claim: is_closed Uᶜ,
    exact is_closed_compl_iff.mpr h1,
    exact is_closed.inter h2 claim,
  },
end

-- a set u is open iff for all element x in it, there exist a neighborhood
-- of x that is contained in u.
lemma is_open_iff_nhds' (u: set Y):
  (∀ x ∈ u, (∃ v ∈ nhds x, v ⊆ u)) ↔ is_open u:=
begin
  split,
  {
    intro y,
    rw ← is_closed_compl_iff,
    rw is_closed_iff_nhds,
    intro x,
    specialize y x,
    intro h,
    change x ∈ u → false,
    intro xu,
    specialize y xu,
    cases y with v y,
    specialize h v,
    cases y with H y,
    specialize h H,
    exact set.inter_compl_nonempty_iff.mp h y,
  },
  {
    intro h,
    intro x,
    intro xu,
    use u,
    split,
    exact is_open.mem_nhds h xu,
    refl,
  }, 
end

-- if an element x is not in a subset u, then {x} and u are disjoint
lemma singleton_not_in {X: Type} (x: X) (u: set X):
  x ∉ u ↔ {x} ∩ u = ∅:=
begin
  split,
  intro hx,
  ext y,
  split,
  {
    intro hy,
    simp,
    change x ∈ u → false at hx,
    apply hx,
    cases hy with hyx hyu,
    cases hyx with hyx1 hyx2,
    exact hyu,
    
  },
  {
    intro h,
    exfalso,
    exact h,
  },

  exact set.singleton_inter_eq_empty.mp,

end

-- if u1 and u2 are disjoint and u3 subset of u2, then u1 and u3 are disjoint
lemma inter_empty_subset {X: Type} (u1: set X) (u2: set X) (u3: set X) :
  u1 ∩ u2 = ∅ ∧ u3 ⊆ u2 → u1 ∩ u3 = ∅ :=
begin
  intro h,
  cases h with h1 h2,
  ext x,
  split,
  {
    intro h3,
    cases h3 with h3 h4,
    have h5: x ∈ u2,
    exact h2 h4,
    have h6: x ∈ u1 ∩ u2,
    split,
    exact h3,
    exact h5,
    rw h1 at h6,
    exact h6,
  },
  {
    intro h,
    exfalso,
    exact h,
  },
end

-- X, Y topological space, if Y is compact, then projection map π1 is closed map
lemma projection_compact_closed (h: is_compact (set.univ: set Y)):
  (is_closed_map (@prod.fst X Y)):=
begin
  unfold is_closed_map,
  intro u,
  intro hu,
  -- want to show complement open
  -- enough to show for each element x in complement, 
  -- there exists nhds of x contained in complement
  rw ← is_open_compl_iff,
  rw ← is_open_iff_nhds',
  intro x,
  intro hx,
  -- we can do this by using tube lemma 
  -- WTS: there exists open v s.t. {x} x Y ⊆ v x Y ⊆ uᶜ
  -- To use tube lemma: we need
  -- 1. is_compact {x}
  -- 2. is_compact Y (we have it in h)
  -- 3. is_open uᶜ
  -- 4. {x} x Y ⊆ uᶜ
  have h1: is_compact {x}, -- 1
  refine is_compact_singleton,

  rw ← is_open_compl_iff at hu, -- 3

  -- we have x ∈ π1(u)ᶜ, WTS: {x} x Y ⊆ uᶜ
  have h2: set.prod {x} (set.univ: set Y) ⊆ uᶜ, -- 4
  rw set.subset_compl_iff_disjoint,
  rw set.mem_compl_iff at hx,
  have h3: set.prod {x} (set.univ: set Y) = prod.fst⁻¹' {x},
  refine set.prod_univ,
  exact X,
  exact set.has_singleton,
  rw h3,
  have h4: disjoint {x} (prod.fst '' u),
  exact set.disjoint_singleton_left.mpr hx,
  have h5: disjoint (prod.fst⁻¹' {x}) (prod.fst⁻¹' (prod.fst '' u)),
  refine disjoint.preimage prod.fst h4,
  exact Y,
  have h6: u ⊆ prod.fst⁻¹' (prod.fst '' u),
  exact set.subset_preimage_image prod.fst u,
  rw set.disjoint_iff_inter_eq_empty at h5,
  rw inter_empty_subset (prod.fst ⁻¹' {x}) (prod.fst ⁻¹' (prod.fst '' u)) u,
  split,
  exact h5,
  exact h6,

  -- use tube lemma (h3 is the result of tube lemma)
  have h3: ∃ (u1 : set X) (v1 : set Y), is_open u1 ∧ is_open v1 ∧ {x} ⊆ u1 ∧ (set.univ: set Y) ⊆ v1 ∧ set.prod u1 v1 ⊆ uᶜ,
  exact generalized_tube_lemma h1 h hu h2,

  cases h3 with u1 h3,
  use u1,
  cases h3 with v1 h3,
  cases h3 with hu1 h3,
  cases h3 with hv1 h3,
  cases h3 with hx1 h3,
  cases h3 with h3 h4,
  split,
  rw mem_nhds_iff,
  use u1,
  split,
  refl,
  split,
  exact hu1,
  exact set.singleton_subset_iff.mp hx1,
  -- prove u1 ⊆ π1(u)ᶜ 
  have h5: v1 = (set.univ: set Y),
  rw ← set.univ_subset_iff,
  exact h3,
  rw h5 at h4,
  rw set.subset_compl_iff_disjoint at h4 ⊢,
  
  ext x1,
  split,
  {
    intro hx2,
    cases hx2 with hx2 hx3,
    -- WTS: if x1 ∈ u1 ∩ π1(u), ∃ x2 ∈ u1 x Y ∩ u = ∅
    have h6: ∃ x2 ∈ u, prod.fst x2 = x1, -- preimage
    exact set.mem_image_iff_bex.mp hx3,
    cases h6 with x2 h6,
    cases h6 with h6 h7,
    have h8: x2.fst ∈ u1,
    exact set.mem_of_eq_of_mem h7 hx2,
    have h9: x2.snd ∈ (set.univ: set Y),
    exact set.mem_univ x2.snd,
    have h10: (x2.fst, x2.snd) ∈ u1.prod set.univ, 
    exact set.mk_mem_prod h8 h9,
    have h11: x2 = (x2.fst, x2.snd),
    exact prod.ext rfl rfl,
    rw ← h11 at h10,
    have h12: x2 ∈ u1.prod set.univ ∩ u,
    exact set.mem_inter h10 h6,
    rw h4 at h12,
    exfalso,
    exact h12,
  },
  {
    intro hx1,
    exfalso,
    exact hx1,
  },
end



def graph {X: Type} {Y: Type} (f: X → Y): set (X × Y) := {(x, f x)| x: X}

-- f: X → Y, Y compact Hausdorff
-- Then f is cts iff the graph of f is closed in X x Y.
lemma cts_map_closed_graph (h1: is_compact (set.univ: set Y)) (h2: t2_space Y):
  continuous f ↔ is_closed (graph f) :=
begin
  split,
  {
    intro h,
    rw ← is_open_compl_iff,
    rw ← is_open_iff_nhds',
    intro xy,
    intro hxy,
    have h3: xy = (xy.fst, xy.snd),
    exact prod.ext rfl rfl,
    rw h3 at hxy,
    have h4: xy.snd ≠ f xy.fst,
    intro h4,
    unfold graph at hxy,
    simp at hxy,
    specialize hxy xy.fst,
    rw h3 at hxy,
    apply hxy,
    rw h4,
    have h5: ∃ (u v : set Y), is_open u ∧ is_open v ∧ xy.snd ∈ u ∧ (f xy.fst) ∈ v ∧ (u ∩ v = ∅),
    exact t2_separation h4,
    cases h5 with u h5,
    cases h5 with v h5,
    cases h5 with hu h5,
    cases h5 with hv h5,
    cases h5 with hxyu h5,
    cases h5 with hxyv h5,
    have h6: is_open (f ⁻¹' u),
    exact continuous_def.mp h u hu,
    have h7: is_open (f ⁻¹' v),
    exact continuous_def.mp h v hv,
    have h8: is_open (set.prod (f ⁻¹' v) u),
    exact is_open.prod h7 hu,
    have claim: xy ∈ set.prod (f ⁻¹' v) u,
    simp,
    exact ⟨hxyv, hxyu⟩,
    use set.prod (f ⁻¹' v) u,
    split,
    exact is_open.mem_nhds h8 claim,
    rw set.subset_compl_iff_disjoint,
    unfold graph,
    ext a,
    split,
    {
      intro ha,
      cases ha with ha1 ha2,
      simp at ha2,
      cases ha2 with afst ha2,
      have ha3: afst = a.fst,
      exact (congr_arg prod.fst ha2).congr_right.mp rfl,
      rw ha3 at ha2,
      rw ← ha2 at ha1,
      simp at ha1,
      cases ha1 with ha ha1,
      have ha4: f a.fst ∈ u ∩ v,
      exact set.mem_inter ha1 ha,
      rw h5 at ha4,
      exact ha4,
    },
    {
      intro ha,
      exfalso,
      exact ha,
    },
  },
  { 
    -- for x in X, s nhds of f(x), Gf ∩ X x (Y - v) closed
    -- π1(Gf ∩ X x (Y - v)) is closed and its compl = f ⁻¹ (s)
    intro h,
    rw continuous_def,
    intro s,
    intro hs,
    have h3: is_closed (set.prod (set.univ: set X) (sᶜ)),
    apply is_closed.prod,
    exact is_closed_univ,
    exact is_closed_compl_iff.mpr hs,
    let u: set (X × Y) := ((set.prod (set.univ: set X) (sᶜ)) ∩ graph f),
    have h4: is_closed u,
    exact is_closed.inter h3 h,
    have h5: is_closed_map (@prod.fst X Y),
    exact projection_compact_closed X Y h1,
    have h6: is_closed (prod.fst '' u),
    exact h5 u h4,
    have h7: prod.fst '' u = (f ⁻¹' s)ᶜ,
    ext x,
    split,
    {
      intro hx,
      intro hx1,
      rw set.mem_preimage at hx1,
      have h8: (x, f x) ∈ graph f,
      unfold graph,
      simp,
      have h11: ∃ a ∈ u, prod.fst a = x,
      exact set.mem_image_iff_bex.mp hx,
      cases h11 with a h11,
      cases h11 with ha h11,
      have h12: a = (a.fst, a.snd),
      exact prod.ext rfl rfl,
      have h13: a.snd = f x,

      rw h11 at h12,
      rw h12 at ha,
      have h10: (x, a.snd) ∈ graph f,
      exact set.mem_of_mem_inter_right ha,
      unfold graph at h10,
      simp at h10,
      exact eq.symm h10,
      rw [h11, h13] at h12,
      rw h12 at ha,
      cases ha with ha1 ha2,
      simp at ha1,
      exact ha1 hx1,
    },
    {
      intro hx,
      simp at hx,
      simp,
      use f x,
      split,
      exact hx,
      unfold graph,
      simp,
    },
    rw ← is_closed_compl_iff,
    rw ← h7,
    exact h6,
  },
end


example (h1: is_open_map f) (h2: function.surjective f) (h3: continuous f) :
  quotient_map f :=
begin
  exact is_open_map.to_quotient_map h1 h3 h2,
end

-- if f : X → Y is continuous, where X is compact and Y is Hausdorff,
-- then f is a closed map
example (h1: continuous f) (h2: is_compact (set.univ: set X)) (h3: t2_space Y) :
  is_closed_map f :=
begin
  unfold is_closed_map,
  intro u,
  intro closeu,
  have h4: u ⊆ (set.univ: set X),
  exact set.subset_univ u,
  have h5: is_compact u,
  exact compact_of_is_closed_subset h2 closeu h4,
  have h6: is_compact (f '' u),
  exact is_compact.image h5 h1,
  exact is_compact.is_closed h6,
end
