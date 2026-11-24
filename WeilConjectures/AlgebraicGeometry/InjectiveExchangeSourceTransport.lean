/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictLocalInjectiveSourceComparison
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

/-! # Source transport on an injective representative

## References

* Stacks Project, Tags 03Q8 and 03Q9.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- Expand the inverse of the fixed injective direct-image comparison
`sourceInjectiveDirectImageIso`. -/
theorem injectiveExchange_source_transport {X S : Scheme.{v}} (f : X ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (J : CochainComplex.Plus (InjectiveObject
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})))
    (q : K.obj ≅ DerivedCategory.Q.obj
      (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) :
    let M₁ := ((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj
    let M : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}) :=
      ⟨M₁, ((InjectiveObject.ι _).mapCochainComplexPlus.obj J).property⟩
    let H := (HomotopyCategory.Plus.quotient _).obj M
    let q' : K ≅ DerivedCategory.Plus.Qh.obj H :=
      DerivedCategory.Plus.ι.preimageIso (Y := DerivedCategory.Plus.Qh.obj H)
        (q ≪≫ (DerivedCategory.quotientCompQhIso _).symm.app M.obj)
    let R := lowerStar AddCommGrpCat.{v + 1} f
    (sourceInjectiveDirectImageIso f K J q).inv =
      (DerivedCategory.quotientCompQhIso _).inv.app
        ((R.mapHomologicalComplex (.up ℤ)).obj M.obj) ≫
      DerivedCategory.Plus.ι.map (R.rightDerivedFunctorPlusUnith.app H) ≫
      DerivedCategory.Plus.ι.map (R.rightDerivedFunctorPlus.map q'.inv) := by
  simp only [sourceInjectiveDirectImageIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, asIso_hom]
  simp only [Functor.map_comp, Functor.mapHomotopyCategoryFactors,
    DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift, NatIso.ofComponents.app, Iso.refl_inv]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]

end AlgebraicGeometry.Etale
