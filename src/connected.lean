import group_theory.group_action 
       category_theory.groupoid
       category_theory.action
       category_theory.category.Groupoid
       quiver
       free

open category_theory

-- a pretransitive action is allowed to be empty
class pretransitive (G X) [group G] [mul_action G X] :=
(trans : ∀ x y : X, ∃ g : G, g • x = y)

-- a groupoid is preconnected when there are enough homs
class preconnected_groupoid (G) [groupoid G] :=
(nonempty_hom : ∀ (a b : G), nonempty (a ⟶ b))

-- the action on cosets is (pre)transitive (indeed the canonical such)
instance (G) [group G] (H : subgroup G) : 
  pretransitive G (quotient_group.quotient H) :=
{ trans := by { rintros ⟨x⟩ ⟨y⟩, use y * x⁻¹, 
        change ⟦_⟧ = ⟦_⟧, apply congr_arg, simp } }

-- a preconnected action gives a preconnected groupoid
instance (G X) [group G] [mul_action G X] [pretransitive G X] :
  preconnected_groupoid (action_category G X) :=
{ nonempty_hom :=
by { intros a b, change nonempty { g : G // _ },
  refine nonempty_subtype.mpr _, exact @pretransitive.trans G X _ _ _ _ _  } }

-- a rooted quiver is `directed_conneted` if there is a path from root to every other node
def directed_connected {G} (p : quiver G) (root : G) := ∀ a, nonempty (p.path root a)

-- a free groupoid is preconnected only if the underlying graph is connected, ish
lemma free_groupoid_directed_connected {G : Groupoid} [preconnected_groupoid G.α] {A : subquiver ♯G.α}
  (hf : is_free_groupoid G A) (root : G.α) : directed_connected ((¡A) ⊕ (¡A)ᵒᵖ) root :=
begin 
  let S := (¡A) ⊕ (¡A)ᵒᵖ,
  have claim : ∀ (a b : G.α), (a ⟶ b) → (nonempty (S.path root a) ↔ nonempty (S.path root b)),
  { apply free_groupoid_induction,
    { exact hf }, { cc }, { cc }, { cc },
    intros a b p hp,
    split; refine nonempty.map _; intro q,
    { apply quiver.path.cons _ _ q (sum.inl ⟨p, hp⟩) },
    { apply quiver.path.cons _ _ q (sum.inr ⟨p, hp⟩) }, },
  intro a, cases preconnected_groupoid.nonempty_hom root a,
  exact (claim root a val).mp ⟨quiver.path.nil⟩,
end
