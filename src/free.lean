import algebra.category.Group category_theory.category.Groupoid category_theory.single_obj category_theory.functor
       category_theory.elements quiver to_mathlib displayed category_theory.action

open category_theory

universes u v

-- The property of being the free group on a subset
-- this definition can be shown to behave well wrt universe levels by
-- comparing with the explicit construction of the free group (which does not raise universe level)
def is_free_group (G) [group.{u} G] (A : set G) : Prop :=
∀ (X : Group.{u}) (f : A → X),
∃! (F : G →* X), f = F ∘ coe

-- The property of being the free groupoid on a subquiver
def is_free_groupoid (G) [groupoid.{v u} G] (A : subquiver ♯G) : Prop :=
∀ (X : Groupoid.{v u}) (x : G → X.α) (f : ¡A →[x] ♯X.α),
∃! (F : functorial x), f = (♮F ⊚ sub_hom A) -- todo figure out why we need brackets

-- a group is free iff it is a free groupoid
lemma free_group_iff_free_groupoid (G) [group G] (A : set G) :
  is_free_group G A ↔
  is_free_groupoid (single_obj G) ((subquiver_equiv G).symm A) :=
begin
  split,
  { intros hfree X,
    change ∀ x : punit → X.α, _,
    rw function.surjective.forall (const_unit_surjective X.α),
    intros x f,
    specialize hfree ⟨End x⟩ (λ a, @f (single_obj.star G) (single_obj.star G) a),
    refine ((functor_equiv x).symm.exists_unique_congr _).mp hfree,
    intro g,
    rw [out_of_unit, out_of_unit],
    refl, },
  { intros hfree X f,
    let x := single_obj.star X.α,
    specialize hfree ⟨single_obj X.α⟩ (λ _, x)
      (λ _ _ a, f a),
    refine ((functor_equiv x).symm.exists_unique_congr _).mpr hfree,
    intro g,
    rw [out_of_unit, out_of_unit],
    refl },
end

-- a functor out of a free groupoid is determined by its values on the generating subquiver
lemma free_groupoid_ext {G X} [groupoid.{v u} G] [groupoid.{v u} X] {A : subquiver ♯G} (hf : is_free_groupoid G A)
   {x : G → X} {P Q : functorial x} :
  P = Q ↔ (♮P ⊚ sub_hom A) = (♮Q ⊚ sub_hom A) :=
begin
  refine ⟨_, _⟩,
  { intro h, rw h },
  intro h,
  rcases hf ⟨X⟩ x (♮P ⊚ sub_hom A) with ⟨R, hR, uR⟩,
  rw [uR P rfl, uR Q h]
end

section covering_map

variables {C : Type*} [category C] {F : C ⥤ Type*} {X : Type*} [groupoid X] (x : F.elements → X)

-- todo is there a name for this construction? or a way to think about it abstractly?
def homsets {a b : C} (f : a ⟶ b) : Type* :=
Π (s : F.obj a) (t : F.obj b) (h : t = F.map f s),
  x ⟨a, s⟩ ⟶ x ⟨b, t⟩

variable {x}

lemma homset_heq {a b : C} {p q : a ⟶ b} {P : homsets x p} {Q : homsets x q} (h : p = q)
  (hs : ∀ (s : F.obj a), P s _ rfl = Q s _ (by rw h)) : P == Q :=
by { cases h, apply heq_of_eq, funext, cases x_3, apply hs }

-- this is a complete triviality, but it seems we need to state it in order to do dependent
-- rewriting
lemma hs_congr {a b : C} {p : a ⟶ b} (P : homsets x p) {s s' : F.obj a} {t t' : F.obj b}
  {h : t = F.map p s} (hs : s = s') (ht : t = t') :
    P s t h = eq_to_hom (by rw hs) ≫ P s' t' (by rwa [hs, ht] at h) ≫ eq_to_hom (by rw ht) :=
by { cases hs, cases ht, simp }

variable (x)
def todo_name_this : disp_cat C :=
{ obj := λ _, unit, 
  mor := λ a b f _ _, Π (s : F.obj a) (t : F.obj b) (h : t = F.map f s),
                      x ⟨a, s⟩ ⟶ x ⟨b, t⟩,
  id := λ a _ s t h, eq_to_hom (by simp [h]),
  comp := λ a b c f g _ _ _ F G s t h, F s _ rfl ≫ G _ t (by simp [h]),
  id_comp := begin
      intros a b _ _ p P,
      apply homset_heq (category.id_comp _),
      intro s,
      rw hs_congr P (functor_to_types.map_id_apply F s) rfl,
      simp,
    end,
  comp_id := begin
      intros a b p _ _ P,
      apply homset_heq (category.comp_id _),
      intro s,
      have : F.map (p ≫ 𝟙 b) s = F.map p s,
      { rw [category.comp_id] },
      rw hs_congr P rfl this,
      simp,
    end,
  assoc := begin
      intros a b c d p q r _ _ _ _ P Q R,
      apply homset_heq (category.assoc _ _ _),
      intro s,
      have : F.map (p ≫ q) s = F.map q (F.map p s),
      { apply functor_to_types.map_comp_apply },
      rw [hs_congr Q rfl this, hs_congr R this rfl],
      simp,
    end }

-- making x functorial is, by design, the same as giving a displayed functor from
-- terminal to todo_name_this
def todo_equiv : functorial x ≃ disp_functor (𝟭 C) (terminal_disp C) (todo_name_this x) :=
{ to_fun := λ G, { obj := λ a _, (),
                   map := λ a b f _ _ _ s t h, G.map ⟨f, h.symm⟩,
                   map_id := begin
                     intros a _,
                     apply heq_of_eq,
                     funext,                      
                     have hh : F.map (𝟙 a) s = t := h.symm,
                     set S : F.elements := ⟨a, s⟩,
                     set T : F.elements := ⟨a, t⟩,
                     set H : S ⟶ T := ⟨𝟙 a, hh⟩,
                     have ST : S = T,
                     { simpa using hh },
                     change G.map H = eq_to_hom (congr_arg x ST),
                     have : eq_to_hom (congr_arg x ST) = G.map (eq_to_hom ST),
                     { symmetry, apply functorial_eq_to_hom_map },
                     rw this,
                     congr,
                     apply faithful.map_injective (category_of_elements.π F),
                     rw eq_to_hom_map,
                     refl, -- the above proof would be a lot easier if we could just rewrite along `s = t` in the beginning
                   end,
                   map_comp := begin
                     intros a b c f g _ _ _ _ _,
                     apply heq_of_eq,
                     funext,
                     change G.map _ = G.map _ ≫ G.map _,
                     rw ←G.map_comp', refl,
                   end },
  inv_fun := λ β, { map := λ a b, match a, b with
                              | ⟨a, s⟩, ⟨b, t⟩ := λ f, β.map ((terminal_functorial C).map f.val).snd s t f.property.symm
                            end,
                    map_id' := begin
                      rintro ⟨a, s⟩,
                      change β.map ((terminal_functorial C).map (𝟙 a)).snd s s _ = _,
                      set A : (terminal_disp C).obj a := (),
                      have : ((terminal_functorial C).map (𝟙 a)).snd = (terminal_disp C).id A,
                      { rw (terminal_functorial C).map_id', refl, },
                      rw this,
                      have foo : β.map ((terminal_disp C).id A) = (todo_name_this x).id (β.obj A),
                      { apply eq_of_heq, apply β.map_id },
                      rw foo, refl,
                    end,
                    map_comp' := begin
                      rintros ⟨a, s⟩ ⟨b, t⟩ ⟨c, u⟩ ⟨f, h⟩ ⟨g, j⟩,
                      set f' := (terminal_functorial C).map f,
                      set g' := (terminal_functorial C).map g,
                      change β.map ((terminal_functorial C).map (f ≫ g)).snd s u _
                        = β.map f'.snd s t _ ≫ β.map g'.snd t u _,
                      transitivity (((todo_name_this x).comp (β.map f'.snd) (β.map g'.snd)) s u _),
                      { repeat {apply congr_fun},
                        have : ((terminal_functorial C).map (f ≫ g)).snd = (terminal_disp C).comp f'.snd g'.snd,
                        { rw (terminal_functorial C).map_comp', refl },   
                        rw this,
                        apply eq_of_heq,
                        apply β.map_comp, },
                      change _ ≫ _ = _ ≫ _,
                      congr,
                      { assumption },
                      { apply heq_congr_arg₂ (β.map f'.snd s),
                        { exact h },
                        apply proof_irrel_heq },
                      { set fl := λ z Z, β.map g'.snd z u Z,
                        change fl _ _ == fl _ _,
                        apply heq_congr_arg₂ fl,
                        { exact h },
                        apply proof_irrel_heq },
                    end },
  left_inv := by { intro G, ext, cases x_1, cases x_2, cases x_3, refl },
  right_inv := begin
    intro β, ext, { refl }, intros a _, rw heq_iff_eq, rintros ⟨⟩,
    apply heq_of_eq, funext, cases _x, cases _x, cases _x, refl, end }

def name_this_todo {G} [groupoid G] {F : G ⥤ Type*} {X} [groupoid X] (x : F.elements → X) :
  disp_groupoid G :=
{ inv := λ a b _ _ p P s t h, inv (P t s (by { rw h,
    exact (functor_to_types.map_hom_map_inv_apply F ((groupoid.iso_equiv_hom _ _).symm p) s).symm })), -- how to make simp find this?
  inv_comp := begin
      intros a b p _ _ P, 
      apply homset_heq (groupoid.inv_comp _),
      intro s,
      change inv _ ≫ _ = eq_to_hom _,
      have : F.map (groupoid.inv p ≫ p) s = s,
      { rw groupoid.inv_comp, apply functor_to_types.map_id_apply },
      rw hs_congr P rfl this,
      simp,
    end,
  comp_inv := begin
      intros a b p _ _ P, 
      apply homset_heq (groupoid.comp_inv _),
      intro s,
      change _ ≫ inv _ = eq_to_hom _,
      have : F.map (p ≫ groupoid.inv p) s = s,
      { rw groupoid.comp_inv, apply functor_to_types.map_id_apply },
      rw hs_congr P this rfl,
      simp,
    end,
  ..todo_name_this x }

-- we would define this wrt to arbitrary displayed category except elements is not defined to be displayed
def subquiver_pullback {C} [category C] (F : C ⥤ Type*) (A : subquiver ♯C) :
  subquiver ♯F.elements :=
λ a b, { f | f.val ∈ A a.fst b.fst }

-- Given an action of a free groupoid, its category of elements
-- is freely generated by the pullback subquiver.
-- This lemma corresponds to the fact that any covering space of a graph is
-- also a graph. In the HoTT formalization of Nielsen-Schreier, it corresponds
-- to the fact that `coequalizers are stable under pullback'
lemma elements_is_free_groupoid {G} [groupoid.{u u} G] {F : G ⥤ Type u} (A : subquiver ♯G) (hf : is_free_groupoid G A) :
  is_free_groupoid F.elements (subquiver_pullback F A) :=
begin
  intros X x,
  let Y := (name_this_todo x).total,
  intro f,
  set ob : G → Y.α := λ x, ⟨x, ()⟩,
  set f' : (¡A →[ob] ♯Y.α) := λ a b p, ⟨p.val, λ s t h,
    @f ⟨_,_⟩ ⟨_,_⟩ ⟨⟨p.val, h.symm⟩, p.property⟩⟩,
  have sane : ∀ P : functorial ob,
    f' = (♮P ⊚ sub_hom A) → 
      ∃ ma : Π {c d : G} (p : c ⟶ d), (name_this_todo x).mor p () (),
        P.map = λ c d p, ⟨p, ma p⟩,
  { intros P hP,
    apply strictify_map,
    rw free_groupoid_ext hf,
    funext,
    change (♮P ⊚ sub_hom A $ e).fst = e.val, 
    rw ←hP },
  rcases hf Y ob f' with ⟨P, hP, uP⟩,
  rcases sane P hP with ⟨ma, hma⟩,
  have sane' : ∀ {c d : G} (p : c ⟶ d), ma p == (P.map p).snd,
  { intros, rw hma, },
  suffices : ∃! y : disp_functor (𝟭 G) (terminal_disp G) (todo_name_this x),
    ∀ {c d : G} (p : c ⟶ d) (hp : p ∈ A c d), (f' ⟨p, hp⟩).snd = y.map (),
  { rw (todo_equiv x).exists_unique_congr,
    { exact this },
    intro z,
    split,
    { intros hyp _ _ _ _, funext, change f _ = _, rw hyp, refl, },
    { intro hyp, funext,
      rcases x_1 with ⟨a, s⟩, 
      rcases x_2 with ⟨b, t⟩, 
      rcases x_3 with ⟨⟨p, h⟩, hp⟩,
      specialize hyp p hp,
      change (f' ⟨p, hp⟩).snd s t h.symm = _, 
      rw hyp, refl, }, },
  { set y : disp_functor (𝟭 G) (terminal_disp G) (todo_name_this x) :=
    { obj := λ _ _, (),
      map := λ a b p a' b' p', ma p,
      map_id := λ a _, calc ma (𝟙 a) == (P.map $ 𝟙 a).snd : sane' _
                                 ... == (todo_name_this x).id () : by { rw P.map_id', refl},
      map_comp := λ a b c f g _ _ _ _ _,
        calc ma (f ≫ g) == (P.map (f ≫ g)).snd : sane' _
                     ... == (P.map f ≫ P.map g).snd : by rw P.map_comp'
                     ... == (todo_name_this x).comp (P.map f).snd (P.map g).snd : by refl
                     ... == (todo_name_this x).comp (ma f) (ma g) : by rw hma },
    refine ⟨y, _, _⟩,
    { exact () },
    { exact () },
    { intros a b p hp,
      change _ = ma p,
      have : f' ⟨p, hp⟩ = P.map p,
      { rw hP, refl }, 
      apply eq_of_heq,
      calc (f' ⟨p, hp⟩).snd == (P.map p).snd : by rw this
                        ... == _ : (sane' _).symm },
    { intros z hyp,
      cases z,
      have : @z_obj = λ _ _, (),
      { funext, exact unit.ext},
      rw this,
      set P' : functorial ob := {
        map := λ _ _ p, ⟨p, @z_map _ _ p () () ()⟩,
        map_id' := λ _, by { apply sigma.ext, refl, apply z_map_id },
        map_comp' := λ _ _ _ _ _, by { apply sigma.ext, refl, apply z_map_comp }, },
      have : P' = P,
      { apply uP,
        ext,
        { refl },
        { refl },
        cases x_3,
        intros a _,
        rw heq_iff_eq,
        rintro ⟨⟩,
        apply heq_of_eq,
        apply congr_fun,
        apply hyp, },
      congr,
      apply funext, intro,
      apply funext, intro,
      apply funext, intro,
      apply funext, rintro ⟨⟩,
      apply funext, rintro ⟨⟩,
      apply funext, rintro ⟨⟩,
      change (P'.map _).snd = _,
      apply eq_of_heq,
      calc (P'.map x_3).snd == (P.map x_3).snd : by rw this
                        ... == ma x_3 : (sane' _).symm
    },
  },
end

lemma free_groupoid_induction {G} [groupoid G] {A : subquiver ♯G} {hf : is_free_groupoid G A}
  {P : Π {a b : G}, (a ⟶ b) → Prop}
    (h_id : ∀ a, P (𝟙 a))
    (h_comp : ∀ {a b c} {f : a ⟶ b} {g : b ⟶ c}, P f → P g → P (f ≫ g))
    (h_inv : ∀ {a b} {f : a ⟶ b}, P f → P (inv f))
    (h_base : ∀ {a b} (f ∈ A a b), P f)
    : ∀ a b (f : a ⟶ b), P f :=
let subgpd : disp_groupoid G :=
{ obj := λ _ , unit,
  mor := λ _ _ p _ _, plift (P p),
  id := λ a _, plift.up (h_id _),
  comp := λ _ _ _ _ _ _ _ _ p q, plift.up (h_comp p.down q.down),
  inv := λ _ _ _ _ _ p, plift.up (h_inv p.down),
  id_comp  := by { intros, cases F, apply heq_of_eq_mp; simp },
  comp_id  := by { intros, cases F, apply heq_of_eq_mp; simp },
  assoc    := by { intros, cases F, apply heq_of_eq_mp; simp },
  inv_comp := by { intros, cases F, apply heq_of_eq_mp; simp },
  comp_inv := by { intros, cases F, apply heq_of_eq_mp; simp },
 } in
begin
  rcases hf subgpd.total (λ a, ⟨a, ()⟩)
  (λ a b p, ⟨p.val, plift.up (h_base p.val p.property)⟩) with ⟨Q, hQ, _⟩,
  intros,
  convert (Q.map f).snd.down,
  set R : functorial id := functorial_comp Q subgpd.to_disp_cat.π,
  change (functorial_id _).map f = R.map f,
  congr,
  rw free_groupoid_ext,
  funext,
  change e.val = ((♮Q ⊚ sub_hom A) e).fst,
  rw ←hQ,
  exact hf,
end

-- being a free group is an isomorphism invariant
lemma is_free_group_mul_equiv {G H : Type u} [group G] [group H] (A : set G) (h : G ≃* H) :
  is_free_group G A ↔ is_free_group H (equiv.set.congr h.to_equiv A) :=
begin
  apply forall_congr,
  intro X,
  set hh := (equiv.Pi_congr_left' _ $ equiv.set.congr.equiv h.to_equiv A),
  apply equiv.forall_congr hh,
  intro f,
  apply equiv.exists_unique_congr (homset_equiv_of_mul_equiv _),
  intro F,
  convert hh.apply_eq_iff_eq_symm_apply.symm,
  rw ←hh.apply_eq_iff_eq_symm_apply,
  refl,
end

instance action_category_inhabited {M X} [monoid M] [mul_action M X] [inhabited X] :
  inhabited (action_category M X) := ⟨⟨single_obj.star M, (default _ : X)⟩⟩

def End_mul_equiv_subgroup {G} [group G] (H : subgroup G) : 
  End (default (action_category G $ quotient_group.quotient H)) ≃* H := 
begin
  refine mul_equiv.trans _ _,
  { exact @mul_action.stabilizer G (quotient_group.quotient H) _  _ (quotient_group.mk 1) },
  { apply_instance },
  { apply mul_equiv.refl }, -- this is a heavy refl
  { rw stabilizer_of_coset_action },
end

end covering_map
