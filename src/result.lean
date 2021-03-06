import arborescence contract category_theory.category.Groupoid

open category_theory

variables {G : Group.{0}} (A : set G) (hfree : is_free_group G A) (H : subgroup G)

def main_theorem : { A' : set H // is_free_group ⟨H⟩ A' } :=
begin
  refine ⟨_, (is_free_group_mul_equiv' _ (End_mul_equiv_subgroup' H)).mp
    (contract (geodesic_subgraph _)
      (@elements_is_free_groupoid ⟨single_obj G⟩
        (action_as_functor G (quotient_group.quotient H)) _ _))⟩,

end