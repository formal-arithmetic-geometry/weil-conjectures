/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.NativeL2.L2NativePunctualWeights
import WeilConjectures.PointCount

/-! # The closed-point geometry used in a rank-one Weil flag

Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, dimension-zero pieces
(blueprint: lem-zl-condensed-point-weil-flags-closed-geometry).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
namespace WeilConjectures.CondensedWeilPointFlags

/-- Every closed point of the ground-field point has cardinality q and degree one,
and every compatible geometric lift is the specified canonical point lift.
Source: latest blueprint, thm-zl-real-mixed-by-curves.proof.md, dimension-zero pieces
(blueprint: lem-zl-condensed-point-weil-flags-closed-geometry).

Proof: the identity structure morphism has itself as a section. The residue-field
map at the image of a section is bijective, so the residue field has cardinality q
and degree one. A compatible lift has second pullback projection equal to the identity.
The canonical point lift is the inverse of this projection; cancelling this isomorphism
identifies the two lifts. No choice of residue embedding affects the result. -/
theorem point_closed_geometry (D : FiniteFieldDatum.{u})
    (x : {x : (pointModel D).left // x ∈ closedPoints (pointModel D).left}) :
    Nat.card ((pointModel D).left.residueField x.val) = D.q ∧
    NativeCondensedModule.localClosedPointDegree D (pointModel D) x = 1 ∧
    ∀ (i : (pointModel D).left.residueField x.val →+* D.k)
      (hi : i.comp ((pointModel D).hom.residueFieldAlgebraMap x.val) =
        algebraMap D.k₀ D.k),
      NativeCondensedModule.localClosedPoint D (pointModel D) x i hi = pointLift D := by
  have hb := Scheme.Hom.bijective_residueFieldAlgebraMap_of_comp_eq_id
    (𝟙 (Spec (.of D.k₀))) (𝟙 _) (Category.id_comp _) x.val
  refine ⟨?_, ?_, ?_⟩
  · exact (Nat.card_eq_of_bijective _ hb).symm.trans D.card_base
  · exact Scheme.Hom.degreeOver_eq_one_of_comp_eq_id
      (𝟙 (Spec (.of D.k₀))) (𝟙 _) (Category.id_comp _) x.val
  · intro i hi
    apply (cancel_mono (pullback.snd (𝟙 (Spec (.of D.k₀)))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))).mp
    change pullback.lift _ (𝟙 _) _ ≫ _ = inv _ ≫ _
    erw [pullback.lift_snd, IsIso.inv_hom_id]

end WeilConjectures.CondensedWeilPointFlags
