/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RingComplexSemilinearExtension
import WeilConjectures.AlgebraicGeometry.RingComplexCechAugmentationHom
import WeilConjectures.AlgebraicGeometry.RingComplexCechScalarModel

/-! # Base change detected by augmented ordered localization models

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 0ALZ](https://stacks.math.columbia.edu/tag/0ALZ)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct ChangeOfRings
namespace AlgebraicGeometry

/-- The normalized scalar-extension map between augmented localization models is a
quasi-isomorphism on every K-flat replacement. -/
theorem ringComplex_cech_baseChange_quasiIso
    (A B : CommRingCat.{u}) [HasDerivedCategory.{w} (RingSiteModules A)]
    [HasDerivedCategory.{w} (RingSiteModules B)] (φ : A →+* B)
    (I : {I : Ideal A // I.FG}) (J : {J : Ideal B // J.FG})
    (h : I.val.map φ = J.val)
    (P : CochainComplex (RingSiteModules A) ℤ)
    (L : CochainComplex (RingSiteModules B) ℤ)
    (εP : P ⟶ ringComplexSingle A) (εL : L ⟶ ringComplexSingle B)
    (hCA : RingComplexHasCechModel A I.val P εP)
    (hCB : RingComplexHasCechModel B J.val L εL)
    (hP : P.IsKFlatTensor) (χ : ringComplexExtensionComplex φ P ⟶ L)
    (hε : ∀ x : (P.X 0).val.obj (op ⟨PUnit.unit⟩),
      ringComplexAugmentationValue εL
          ((χ.f 0).val.app (op ⟨PUnit.unit⟩)
            ((toSheafify ⊥ (SheafOfModules.changeOfRingsPresheaf
              (ringSiteMap φ) (P.X 0)).presheaf).app (op ⟨PUnit.unit⟩)
                ((1 : B) ⊗ₜ[A, φ] x))) = φ (ringComplexAugmentationValue εP x)) :
    QuasiIso χ := by
  obtain ⟨εE, hCE, hεE⟩ := ringComplex_cech_scalar_model A B φ I J h P εP hCA hP
  have haug : χ ≫ εL = εE := by
    apply HomologicalComplex.to_single_hom_ext
    apply (cancel_mono (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (ringComplexUnit B)).hom).mp
    apply ringComplexExtension_hom_ext φ (P.X 0) (ringComplexUnit B)
    intro x
    exact (hε x).trans (hεE x).symm
  obtain ⟨ψ, hψ⟩ := (ringComplex_cech_augmentation_hom_bijective B J L
    (ringComplexExtensionComplex φ P) εL εE hCB hCE).surjective
      (DerivedCategory.Q.map εL)
  have hright : DerivedCategory.Q.map χ ≫ ψ = 𝟙 _ := by
    apply (ringComplex_cech_augmentation_hom_bijective B J
      (ringComplexExtensionComplex φ P) (ringComplexExtensionComplex φ P)
      εE εE hCE hCE).injective
    simp only [Category.assoc, hψ, ← Functor.map_comp, haug, Category.id_comp]
  have hleft : ψ ≫ DerivedCategory.Q.map χ = 𝟙 _ := by
    apply (ringComplex_cech_augmentation_hom_bijective B J L L εL εL hCB hCB).injective
    simp only [Category.assoc, ← Functor.map_comp, haug, hψ, Category.id_comp]
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso (RingSiteModules B) χ).mp
  exact ⟨⟨ψ, hright, hleft⟩⟩

end AlgebraicGeometry
