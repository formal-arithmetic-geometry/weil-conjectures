/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedRHomAlgebraModule
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import WeilConjectures.AlgebraicGeometry.SheafAlgebraHomAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Deriving the algebra-valued Hom adjunction and comparing its localization

## References

* [Stacks Project, Tag 0BV0](https://stacks.math.columbia.edu/tag/0BV0)
* [Stacks Project, Tag 0BV1](https://stacks.math.columbia.edu/tag/0BV1)
* [Stacks Project, Tag 0A6F](https://stacks.math.columbia.edu/tag/0A6F)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
-/

@[expose] public section

universe u w wB

open CategoryTheory TopologicalSpace

attribute [local instance] SheafOfModules.isGrothendieckAbelian

namespace AlgebraicGeometry

/-- The localization of exact scalar restriction is left adjoint to the explicit
algebra-valued derived Hom. -/
theorem sheafAlgebra_mapDerivedCategory_adjunction
    (Y : Scheme.{u}) (B : Y.CommAlgebraSheaf) (hB : B.toModule.IsQuasicoherent)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wB} (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).obj B.right))] :
    Nonempty ((SheafOfModules.restrictScalars.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).map B.hom)).mapDerivedCategory ⊣
          derivedRHomAlgebraModule Y B hB) := by
  let C := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let D := SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology Y)
      (forget₂ CommRingCat RingCat)).obj B.right)
  let R := sheafAlgebraHom Y B
  let I := sheafAlgebraHomResolution Y
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let qD := HomotopyCategory.quotient D (ComplexShape.up ℤ)
  let i := toSheafAlgebraHomResolution Y
  have hi (K : CochainComplex C ℤ) : QuasiIso (i.app K) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app C K).2
  let t := Functor.whiskerLeft (I ⋙ q) R.rightDerivedFunctorUnit
  have ht (K : CochainComplex C ℤ) : IsIso (t.app K) := by
    change IsIso (R.rightDerivedFunctorUnit.app (q.obj (I.obj K)))
    have : (I.obj K).IsKInjective := by
      dsimp [I, sheafAlgebraHomResolution]
      infer_instance
    infer_instance
  have : IsIso t := NatIso.isIso_of_isIso_app t
  let j := Functor.whiskerRight i (DerivedCategory.Q (C := C))
  have hj (K : CochainComplex C ℤ) : IsIso (j.app K) := by
    let := hi K
    change IsIso (DerivedCategory.Q.map (i.app K))
    infer_instance
  have : IsIso j := NatIso.isIso_of_isIso_app j
  let e : DerivedCategory.Q ⋙ R.rightDerivedFunctor ≅
      I ⋙ R.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.leftUnitor DerivedCategory.Q).symm |> fun e₀ ↦
      Functor.isoWhiskerRight (e₀ ≪≫ asIso j) R.rightDerivedFunctor ≪≫
      Functor.associator I DerivedCategory.Q R.rightDerivedFunctor ≪≫
      Functor.isoWhiskerLeft I
        (Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso C).symm
          R.rightDerivedFunctor ≪≫ Functor.associator q DerivedCategory.Qh
          R.rightDerivedFunctor) ≪≫
      (Functor.associator I q (DerivedCategory.Qh ⋙ R.rightDerivedFunctor)).symm ≪≫
      (asIso t).symm ≪≫
      Functor.associator I q (R.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh) ≪≫
      Functor.isoWhiskerLeft I
        ((Functor.associator q (R.mapHomotopyCategory (ComplexShape.up ℤ))
          DerivedCategory.Qh).symm ≪≫
        Functor.isoWhiskerRight (R.mapHomotopyCategoryFactors (ComplexShape.up ℤ))
          DerivedCategory.Qh ≪≫
        Functor.associator (R.mapHomologicalComplex (ComplexShape.up ℤ)) qD
          DerivedCategory.Qh ≪≫
        Functor.isoWhiskerLeft (R.mapHomologicalComplex (ComplexShape.up ℤ))
          (DerivedCategory.quotientCompQhIso D))
  obtain ⟨ec⟩ := derivedRHomAlgebraModule_comparison Y B hB
  let er := (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) (DerivedCategory D)).preimageIso
      (e ≪≫ ec.symm)
  obtain ⟨adj⟩ := sheafAlgebraHom_adjunction Y B
  exact ⟨adj.mapDerivedCategoryRightDerivedAdjunction.ofNatIsoRight er⟩

end AlgebraicGeometry
