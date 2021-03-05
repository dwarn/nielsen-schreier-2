import connected

noncomputable theory

variables {V : Type*} {G : quiver V} {root : V}

def length : Π {a : V} (p : G.path root a), ℕ
| _  quiver.path.nil := 0
| _  (quiver.path.cons p _) := length p + 1

variable (H : directed_connected G root)

/-- A path to `root` of minimal length. -/
def shortest_path (a : V) : G.path root a :=
well_founded.min (measure_wf $ λ p : G.path root a, length p) set.univ
  (@set.univ_nonempty _ (H a))

/-- The length of a path is at least the length of the shortest path -/
lemma shortest_path_spec {a : V} (p : G.path root a) :
  length (shortest_path H a) ≤ length p :=
begin
  have : ¬ (length p < length (shortest_path H a)) :=
    well_founded.not_lt_min (measure_wf _) set.univ _ trivial,
  simpa using this,
end

/-- The geodesic subgraph. For each non-root vertex, there is an edge to a parent:
some vertex that is closer to `root`. -/
def geodesic_subgraph : subquiver G :=
λ a b e, ∃ p : G.path root a, shortest_path H b = quiver.path.cons p e

-- todo: write this idiomatically
lemma paths_are_unique : ∀ {s : V} {p q : (¡geodesic_subgraph H).path root s}, p = q
| _ (quiver.path.nil) := begin
  rintro ( _ | _ ),
  { refl },
  exfalso,
  rcases q_ᾰ_1 with ⟨_, _, h⟩,
  have : length (shortest_path H root) ≤ 0 :=
    shortest_path_spec H quiver.path.nil,
  rw h at this,
  change _ + 1 ≤ 0 at this,
  simpa only [nonpos_iff_eq_zero] using this,
end
| t (quiver.path.cons p e) := begin
  rcases e with ⟨_, _, h⟩,
  rintro ( _ | _ ),
  { have : length (shortest_path H root) ≤ 0 :=
      shortest_path_spec H quiver.path.nil,
    rw h at this,
    change _ + 1 ≤ 0 at this,
    simpa only [nonpos_iff_eq_zero] using this },
  { rcases q_ᾰ_1 with ⟨_, _, hq⟩,
    rw h at hq,
    cases hq,
    congr,
    apply paths_are_unique }
end

lemma geodesic_path : ∀ (gas : ℕ) (t : V), length (shortest_path H t) ≤ gas →
      (¡geodesic_subgraph H).path root t :=
begin -- todo: write this idiomatically
  intro gas,
  induction gas with gas ih,
  { intros t h,
    have : ∃ p, p = shortest_path H t, 
    { refine ⟨_, rfl⟩ },
    rcases (classical.indefinite_description _ this) with ⟨p, hp⟩,
    cases p with s t p e,
    { exact quiver.path.nil },
    { exfalso, -- out of gas
      rw ←hp at h,
      simpa using h } },
  { intros t h,
    have : ∃ p, p = shortest_path H t, 
    { refine ⟨_, rfl⟩ },
    rcases (classical.indefinite_description _ this) with ⟨p, hp⟩,
    cases p with s t p e,
    { exact quiver.path.nil },
    { refine quiver.path.cons _ ⟨e, p, hp.symm⟩,
      apply ih,
      rw ←hp at h,
      change _ + 1 ≤ _ + 1 at h,
      rw add_le_add_iff_right at h,
      exact le_trans (shortest_path_spec H p) h } }
end

instance geodesic_tree : (¡geodesic_subgraph H).is_tree root :=
{ favourite := λ b, geodesic_path H _ b (le_refl _),
  is_favourite := λ b q, paths_are_unique H }