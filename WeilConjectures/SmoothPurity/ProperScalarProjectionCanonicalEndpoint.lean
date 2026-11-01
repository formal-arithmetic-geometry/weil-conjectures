/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.ProperScalarProjectionCanonicalMate

/-! # Canonical scalar projection endpoint transport -/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

/-- The fixed intrinsic projection arrow has the prescribed constant-coefficient endpoint.
Source: Stacks Tags 07A4 and 07A6 (blueprint: helper-proper-scalar-canonical-endpoint).

Proof: apply the finite scalar proper projection presentation, then transport both endpoints
through the intrinsic realization equivalence and its unit and counit isomorphisms. Naturality
of the right derived projection map supplies the arrow commutativity. This is independent of
the scalar mate normalization calculation. -/
theorem properScalarMate_canonical_endpoint_arrowIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (g : Z ⟶ Y)
    (P : DerivedCategory
      (Sheaf (ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    Nonempty (canonicalScalarProjectionArrow φ g P ≅ Arrow.mk
      (((ProEtale.rightDerivedLowerStarProjectionMap
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).app P).app
        ((constantSheaf (ProEt.topology Y)
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor _ 0).obj
            ((ModuleCat.restrictScalars.{u + 1} φ.ulift).obj
              (ModuleCat.of (ULift.{u + 1, u} B) (ULift.{u + 1, u} B))))))) := by
  let aZ := Classical.choice (PurCompactSupport.tensorModel_exists Z (proEtaleConstantRing Z A))
  let aY := Classical.choice (PurCompactSupport.tensorModel_exists Y (proEtaleConstantRing Y A))
  let K := (sfIntrinsicDerivedEquivalence Z A).functor.obj P
  let Q := ((constantSheaf (ProEt.topology Y)
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))).mapDerivedCategory.obj
      ((DerivedCategory.singleFunctor _ 0).obj
        ((ModuleCat.restrictScalars.{u + 1} φ.ulift).obj
          (ModuleCat.of (ULift.{u + 1} B) (ULift.{u + 1} B)))))
  let L := (sfIntrinsicDerivedEquivalence Y A).functor.obj Q
  obtain ⟨h⟩ := finiteScalarProperProjection_presentation A g aZ aY K L
  let EY := sfIntrinsicDerivedEquivalence Y A
  let EZ := sfIntrinsicDerivedEquivalence Z A
  let π := Functor.uncurry.map (ProEtale.rightDerivedLowerStarProjectionMap
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g)
  let x := (EZ.inverse.obj K, EY.inverse.obj L)
  let f := π.app x
  let h₀ := EY.inverse.mapArrow.mapIso h
  let h₁ : Arrow.mk (EY.inverse.map (EY.functor.map f)) ≅ Arrow.mk f :=
    Arrow.isoMk (EY.unitIso.app _).symm (EY.unitIso.app _).symm
      (EY.unitIso.inv.naturality f).symm
  let e := Iso.prod (EZ.unitIso.app P).symm (EY.unitIso.app Q).symm
  let h₂ : Arrow.mk (π.app x) ≅ Arrow.mk (π.app (P, Q)) :=
    Arrow.isoMk ((Functor.uncurry.obj (ProEtale.derivedTensorRightDerivedLowerStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g)).mapIso e)
      ((Functor.uncurry.obj (ProEtale.rightDerivedLowerStarDerivedTensorLeftDerivedUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g)).mapIso e) (π.naturality e.hom)
  exact ⟨h₀ ≪≫ h₁ ≪≫ h₂⟩

end WeilConjectures
