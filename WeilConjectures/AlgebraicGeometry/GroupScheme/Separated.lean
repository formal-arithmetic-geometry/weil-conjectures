/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Group schemes over a field are separated

Let `G` be a group scheme locally of finite type over a field `k`. The unit section
`e : Spec k ⟶ G` is a closed immersion, being a section of a morphism locally of finite type
whose image is a closed point. The shear automorphism `(g, h) ↦ (g, g⁻¹ h)` of `G ×_k G` carries
the diagonal of `G` to the base change `G ⟶ G ×_k G`, `g ↦ (g, e)`, of `e`, so the diagonal is a
closed immersion and `G` is separated over `k` (Stacks 047L).

## Main statements

- `AlgebraicGeometry.isClosedImmersion_of_comp_eq_id`: a section of a morphism locally of finite
  type to the spectrum of a field is a closed immersion.
- `AlgebraicGeometry.GrpObj.isSeparated_hom`: a group scheme locally of finite type over a field
  is separated.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- **A rational point of a scheme locally of finite type over a field is a closed immersion.**
If `X` is locally of finite type over a field `k` and `s : Spec k ⟶ X` is a section of the
structure morphism, then `s` is a closed immersion. -/
theorem isClosedImmersion_of_comp_eq_id {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (s : Spec (.of k) ⟶ X) (hs : s ≫ f = 𝟙 _) :
    IsClosedImmersion s :=
  sorry

/-- **Group schemes over a field are separated.** A group scheme `G` locally of finite type over
a field `k` is separated over `k`: the shear automorphism `(g, h) ↦ (g, g⁻¹ h)` of `G ×_k G`
carries the diagonal to the base change of the unit section, which is a closed immersion. -/
@[stacks 047L]
instance GrpObj.isSeparated_hom (G : Over (Spec (.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] : IsSeparated G.hom :=
  sorry

end AlgebraicGeometry
