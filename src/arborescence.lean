import connected

noncomputable theory

variables {V : Type*} {G : quiver V} [inhabited V]

local notation `root` := default V

def quiver.path.length {a} : Π {b : V} (p : quiver.path G a b), ℕ
| _  quiver.path.nil       := 0
| _ (quiver.path.cons p _) := p.length + 1

variables [directed_connected G] (G)

/-- A path to `root` of minimal length. -/
def shortest_path (a : V) : G.path root a :=
well_founded.min (measure_wf $ λ p : G.path root a, p.length) set.univ set.univ_nonempty

/-- The length of a path is at least the length of the shortest path -/
lemma shortest_path_spec {a : V} (p : G.path root a) :
  (shortest_path G a).length ≤ p.length :=
begin
  have : ¬ (p.length < (shortest_path G a).length) :=
    well_founded.not_lt_min (measure_wf _) set.univ _ trivial,
  simpa using this,
end

/-- The geodesic subgraph. For each non-root vertex, there is an edge from a parent:
    some vertex that is closer to `root`. -/
def geodesic_subgraph : subquiver G :=
λ a b e, ∃ p : G.path root a, shortest_path G b = quiver.path.cons p e

-- todo: write this idiomatically
lemma paths_are_unique : ∀ {s : V} {p q : (¡geodesic_subgraph G).path root s}, p = q
| _ (quiver.path.nil) := begin
  rintro ( _ | _ ),
  { refl },
  exfalso,
  rcases q_ᾰ_1 with ⟨_, _, h⟩,
  have : (shortest_path G root).length ≤ 0 :=
    shortest_path_spec G quiver.path.nil,
  rw h at this,
  change _ + 1 ≤ 0 at this,
  simpa only [nonpos_iff_eq_zero] using this,
end
| t (quiver.path.cons p e) := begin
  rcases e with ⟨_, _, h⟩,
  rintro ( _ | _ ),
  { have : (shortest_path G root).length ≤ 0 :=
      shortest_path_spec G quiver.path.nil,
    rw h at this,
    change _ + 1 ≤ 0 at this,
    simpa only [nonpos_iff_eq_zero] using this },
  { rcases q_ᾰ_1 with ⟨_, _, hq⟩,
    rw h at hq,
    cases hq,
    congr,
    apply paths_are_unique }
end

def geodesic_path : Π (gas : ℕ) (t : V), (shortest_path G t).length ≤ gas →
      (¡geodesic_subgraph G).path root t :=
begin -- todo: write this idiomatically
  intro gas,
  induction gas with gas ih,
  { intros t h,
    have : ∃ p, p = shortest_path G t, 
    { refine ⟨_, rfl⟩ },
    rcases (classical.indefinite_description _ this) with ⟨p, hp⟩,
    cases p with s t p e,
    { exact quiver.path.nil },
    { exfalso, -- out of gas
      rw ←hp at h,
      simpa using h } },
  { intros t h,
    have : ∃ p, p = shortest_path G t, 
    { refine ⟨_, rfl⟩ },
    rcases (classical.indefinite_description _ this) with ⟨p, hp⟩,
    cases p with s t p e,
    { exact quiver.path.nil },
    { refine quiver.path.cons _ ⟨e, p, hp.symm⟩,
      apply ih,
      rw ←hp at h,
      change _ + 1 ≤ _ + 1 at h,
      rw add_le_add_iff_right at h,
      exact le_trans (shortest_path_spec G p) h } }
end

instance geodesic_tree : is_arbor ¡geodesic_subgraph G :=
{ unique_path := λ b,
  { default := geodesic_path G _ b (le_refl _),
    uniq := λ _, paths_are_unique G } }