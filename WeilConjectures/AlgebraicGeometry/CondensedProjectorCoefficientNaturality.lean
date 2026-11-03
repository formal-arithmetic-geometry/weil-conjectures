/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedArtinSchreier
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsRegularEnd
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients

/-! Naturality of the condensed Artin–Schreier character projector under coefficients.

Source: latest blueprint, lem-fd-first-formula proof, coefficient paragraph
(blueprint: lem-fd-unit-punctured-kernel-coefficient-comparison).
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- The Artin–Schreier character projector commutes with a coefficient map when the finite-field
cardinality is a unit in the source coefficient ring. -/
theorem condensed_projector_coefficient_naturality
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (a : Λ ⟶ Λ') [IsMonHom a] (k : Type u) [Field k] [Fintype k]
    (hq : IsUnit (Fintype.card k : MonObj.Γ Λ))
    (ψ : AddChar k (MonObj.Γ Λ)) :
    (condensedArtinSchreierProjector Λ k ψ).hom ≫
        (ProEtale.lowerStar Ab.{u + 1}
          (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))).map
            (coefficientMap a (AffineSpace PUnit (Spec (.of k)))) =
      (ProEtale.lowerStar Ab.{u + 1}
        (AffineSpace.artinSchreierMap PUnit (Spec (.of k)) (Fintype.card k))).map
          (coefficientMap a (AffineSpace PUnit (Spec (.of k)))) ≫
        (condensedArtinSchreierProjector Λ' k
          ((MonObj.Γ.map a).toMonoidHom.compAddChar ψ)).hom := by
  sorry

end AlgebraicGeometry.ProEtale
