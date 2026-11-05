/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Basic

/-!
# Order of vanishing of elements of local rings

- `AlgebraicGeometry.Scheme.Hom.functionFieldIso`: the function fields of a nonempty open
  subscheme and of the ambient integral scheme agree.
- `AlgebraicGeometry.Scheme.ord_functionFieldIso`: the order of vanishing is invariant under open
  immersions.
- `AlgebraicGeometry.Scheme.ord_algebraMap_stalk`: the order of vanishing of an element of a local
  ring is its ring-theoretic order.
-/

@[expose] public section

open Order

namespace AlgebraicGeometry

section OpenImmersion

open CategoryTheory

variable {U X : Scheme.{u}} (i : U ⟶ X) [IsOpenImmersion i] [IsIntegral X] [IsIntegral U]

/-- The isomorphism `k(X) ≅ k(U)` of function fields induced by an open immersion `i : U ⟶ X`
of integral schemes: the stalk map at the generic point. -/
noncomputable def Scheme.Hom.functionFieldIso : X.functionField ≅ U.functionField :=
  X.presheaf.stalkCongr (.of_eq (genericPoint_eq_of_isOpenImmersion i).symm) ≪≫
    asIso (i.stalkMap (genericPoint U))

lemma Scheme.Hom.functionFieldIso_algebraMap (z : U) (s : X.presheaf.stalk (i z)) :
    i.functionFieldIso.hom (algebraMap _ X.functionField s) =
      algebraMap _ U.functionField (i.stalkMap z s) := by
  have h := Scheme.Hom.stalkSpecializes_stalkMap_apply i (genericPoint U) z
    ((genericPoint_spec U).specializes trivial) s
  refine Eq.trans ?_ h
  change i.stalkMap _ (X.presheaf.stalkSpecializes
    (Inseparable.of_eq (genericPoint_eq_of_isOpenImmersion i).symm).ge
    (X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) s)) = _
  rw [TopCat.Presheaf.stalkSpecializes_comp_apply]

/-- The order of vanishing is invariant under open immersions: for an open immersion
`i : U ⟶ X` of locally noetherian integral schemes, `ord_z(f|_U) = ord_{i z}(f)`. -/
theorem Scheme.ord_functionFieldIso [IsLocallyNoetherian X] [IsLocallyNoetherian U] (z : U)
    (f : X.functionField) : U.ord (i.functionFieldIso.hom f) z = X.ord f (i z) := by
  by_cases hz : coheight z = 1
  · have hz' : coheight (i z) = 1 := (coheight_eq_of_isOpenImmersion i).trans hz
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hz, Scheme.ord_eq_ordHom_of_coheight_eq_one hz']
    have : Ring.KrullDimLE 1 (X.presheaf.stalk (i z)) := krullDimLE_of_coheight_le hz'.le
    have : Ring.KrullDimLE 1 (U.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
    congr 2
    exact Ring.ordFrac_ringEquiv (asIso (i.stalkMap z)).commRingCatIsoToRingEquiv
      i.functionFieldIso.commRingCatIsoToRingEquiv (i.functionFieldIso_algebraMap z) f
  · have hz' : coheight (i z) ≠ 1 := (coheight_eq_of_isOpenImmersion i).trans_ne hz
    rw [Scheme.ord_eq_zero_of_coheight_neq_one hz, Scheme.ord_eq_zero_of_coheight_neq_one hz']

end OpenImmersion

end AlgebraicGeometry
