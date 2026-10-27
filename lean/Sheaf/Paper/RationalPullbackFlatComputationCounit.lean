/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C8
-/
module

public import Sheaf.Paper.RationalRealizationPullbackComparison
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Sheaf.AlgebraicGeometry.ProEtaleAlgebraicInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Sheaf.Paper.KFlatRingedToposPullback

/-!
# Rational pullback computation on flat-term K-flat complexes

Source: Stacks Tags 0G7E and 06YY; Bhatt--Scholze, Remark 6.8.15.
(blueprint: lem-per-rational-pullback-flat-computation-counit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genInjectivity false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard
  Functor.sheafPullbackConstruction.sheafPullback proEtaleRingInverseImageComp
  LocallyRingedSpace.comp PresheafedSpace.comp

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E]
  [FiniteDimensional ℚ_[l] E]

private noncomputable def rationalScalarTensorExtension {T : Scheme.{u}}
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    pbcModules T R ⥤ pbcModules T R :=
  (show pbcModules T R ⥤ _root_.PresheafOfModules.{u + 1}
    ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj from
    { obj := SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} (𝟙 R)
      map a :=
        { app := fun V ↦ (ModuleCat.extendScalars ((𝟙 R : R ⟶ R).hom.app V).hom).map (a.val.app V)
          naturality := SheafOfModules.changeOfRingsHom_naturality (𝟙 R) _ a }
      map_id M := by
        apply _root_.PresheafOfModules.hom_ext
        intro V
        simp
        rfl
      map_comp a b := by
        apply _root_.PresheafOfModules.hom_ext
        intro V
        simp }) ⋙ PresheafOfModules.sheafification
          (𝟙 ((sheafCompose (ProEt.topology T)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).obj)

/-- The rational pullback computation counit is invertible on flat-term K-flat complexes.
Source: Stacks Tags 0G7E and 06YY; Bhatt--Scholze, Remark 6.8.15.
(blueprint: lem-per-rational-pullback-flat-computation-counit).

Proof: present pro-etale module inverse image by its algebraic inverse-image data.
The underlying inverse-image functor preserves finite limits. The ringed-topos
K-flat pullback theorem therefore says that inverse image followed by identity
scalar extension preserves a K-flat complex whose terms are flat on the site.
On this pulled-back K-flat complex the scalar-extension computation counit is
invertible. The other factors in the rational pullback computation counit are
images or components of natural isomorphisms, so their composite is invertible. -/
theorem rationalPullComplexCounit_isIso_of_flatTerms {S T : Scheme.{u}} (g : S ⟶ T)
    (c : (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj
      (rationalCoefficientSheaf l T E) ⟶ rationalCoefficientSheaf l S E)
    (P : CochainComplex (pbcModules T (rationalCoefficientSheaf l T E)) ℤ)
    (hp : P.IsKFlatIndependentCoefficients)
    (hf : ∀ n : ℤ, SheafOfModules.IsFlatOnSite (J := ProEt.topology T)
      (R := rationalCoefficientSheaf l T E) (P.X n)) :
    IsIso (rationalPullComplexCounit l E g c P) := by
  let R := rationalCoefficientSheaf l T E
  let RI := (proEtaleSheafInverseImage g CommRingCat.{u + 1}).obj R
  obtain ⟨I, hI⟩ := proEtaleAlgebraicInverseImage_exists g R
  have : PreservesFiniteLimits (proEtaleSheafInverseImage g (Type (u + 1))) :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage g (𝟙 T)).2.2.2.1
  let U := I.modules ⋙ rationalScalarTensorExtension RI
  have hUeq : U = proEtaleRingModulePullback g R RI (Iso.refl _) := by
    dsimp only [U]
    rw [hI]
    rfl
  have : U.Additive := by rw [hUeq]; infer_instance
  have hobj (M) : U.obj M =
      SheafOfModules.changeOfRings.{u, u + 1, u + 1} (𝟙 RI) (I.modules.obj M) := rfl
  have hmap : ∀ {M N} (f : M ⟶ N), U.map f = eqToHom (hobj M) ≫
      SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} (𝟙 RI)
        (I.modules.obj M) (I.modules.map f) ≫ eqToHom (hobj N).symm := by
    intro M N f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  have hU := (SheafOfModules.isKFlat_ringedToposPullback
    (proEtaleSheafInverseImage g (Type (u + 1)))
    (proEtaleSheafDirectImage g (Type (u + 1)))
    (proEtaleSheafAdjunction g (Type (u + 1))) I (𝟙 RI) U hobj hmap P hp hf).1
  simp only [U, hI] at hU
  have := pbcExtensionCounit_isIso c
    (((proEtaleRingModulePullback g R RI (Iso.refl _)).mapHomologicalComplex
      (.up ℤ)).obj P) hU
  unfold rationalPullComplexCounit pbcComplexCounit
  infer_instance

end AlgebraicGeometry.Scheme
