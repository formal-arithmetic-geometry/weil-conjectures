module

public import Sheaf.AlgebraicGeometry.SolvableGroupStructure

/-! # Borel subgroups over an arbitrary field

Source: Milne, Algebraic Groups (2017), Definition 17.6 and Chapter 21, p.424
(blueprint: def-sfb-field-borel-subgroup).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A smooth connected solvable closed subgroup maximal among such subgroups.
This field-relative predicate does not require the field to be algebraically closed.
Solvability is the recorded finite closed subnormal-series predicate.
Source: Milne, Definition 17.6 and Chapter 21, p.424
(blueprint: def-sfb-field-borel-subgroup). -/
def IsFieldBorel {F : Type u} [Field F] {B H : Grp (Over (Spec (.of F)))}
    (i : B ⟶ H) : Prop :=
  IsClosedSubgroupScheme i.hom.hom ∧ Smooth B.X.hom ∧ ConnectedSpace B.X.left ∧
    SolvableGroupStructure.IsSolvable B ∧
    ∀ (D : Grp (Over (Spec (.of F)))) (j : D ⟶ H),
      IsClosedSubgroupScheme j.hom.hom → Smooth D.X.hom → ConnectedSpace D.X.left →
      SolvableGroupStructure.IsSolvable D → ∀ f : B ⟶ D, f ≫ j = i → IsIso f

end AlgebraicGeometry
