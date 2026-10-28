/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CompactSupportNativeSystemEvaluation
public import Sheaf.Paper.SemilinearSystemModels
public import Sheaf.AlgebraicGeometry.VaryingRingOperations
import all Sheaf.AlgebraicGeometry.VaryingRingOperations
import all Sheaf.AlgebraicGeometry.TowerOpenBetaNormalization
import Sheaf.Paper.SemilinearDerivedCalculus
import Sheaf.Paper.CoefNativeFiniteTensorSupport

/-! Finite coefficient evaluation of the native ordinary tensor counit.

Source: Stacks, Modules on Sites, Tag 0E8I.
(blueprint: new-coef-native-open-tensor-ordinary-counit-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.SemilinearSections
open CategoryTheory.MonoidalCategory
namespace WeilConjectures.CoefSupportOpenTensor

attribute [-instance] SemilinearSections.hasDerived SemilinearSections.moduleAbelian
  SemilinearSections.abelianSheafify SemilinearSections.locallyBijective
  SemilinearSections.sequenceSmall SemilinearSections.sliceSmall

attribute [local irreducible] Functor.leftAdjoint SheafOfModules.monoidalCategory

private theorem evaluatedCounit
    {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
    [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') {E : A ⥤ C} {H : B ⥤ D}
    (q : R ⋙ E ≅ H ⋙ R')
    [IsIso ((mateEquiv a b).symm q.hom).natTrans]
    (T : B) [IsIso (b.counit.app (H.obj T))] : IsIso (H.map (a.counit.app T)) := by
  have h := mateEquiv_counit_symm a b q.hom T
  have : IsIso (((mateEquiv a b).symm q.hom).app (R.obj T) ≫
      H.map (a.counit.app T)) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (((mateEquiv a b).symm q.hom).app (R.obj T)) (H.map (a.counit.app T))

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/--
The ordinary native open tensor counit is invertible after every coefficient
level evaluation. The proof identifies the evaluated sequence-site adjunction
with the localized ordinary extension adjunction for the corresponding
coefficient quotient and applies the ordinary projection formula of Tag 0E8I.
Source: Stacks, sites-modules.tex, Tag 0E8I, proof on each coefficient quotient.
(blueprint: new-coef-native-open-tensor-ordinary-counit-evaluation).
-/
theorem nativeOpenTensor_ordinary_counit_evaluation_isIso
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (M : coefficientSequenceModules.{u, u} l E X)
    (N : coefficientSequenceModules.{u, u} l E Z) (n : ℕ) :
    IsIso ((coefficientSequenceEvaluation l E Z n).map
      ((AlgebraicGeometry.ProEtale.VaryingRing.moduleJAdj
        (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j).counit.app
        (ordinaryTensor.{u + 1, u, u}
          (coefficientSequenceTopology (ProEt.topology Z))
          (coefficientSequenceCommRingSheaf l E Z)
          ((AlgebraicGeometry.ProEtale.VaryingRing.extension
            (compactSupportSystemLevel l E) (compactSupportSystemQuotient l E) j).obj M) N))) := by
  let R := compactSupportSystemLevel l E
  let φ := compactSupportSystemQuotient l E
  let a := ProEtale.VaryingRing.moduleJAdj R φ j
  let b := ProEtale.StrictTower.moduleJAdj (R n) j
  let eX := ProEtale.VaryingRing.eval R φ X n
  let eZ := ProEtale.VaryingRing.eval R φ Z n
  let q := ProEtale.VaryingRing.moduleEvalG R φ j n
  let δ := ((mateEquiv a b).symm q.hom).natTrans
  have hδ : IsIso δ := ProEtale.VaryingRing.ordinaryOpenMateIso R φ j n
  let T := ordinaryTensor.{u + 1, u, u}
    (coefficientSequenceTopology (ProEt.topology Z))
    (coefficientSequenceCommRingSheaf l E Z)
    ((ProEtale.VaryingRing.extension R φ j).obj M) N
  let : EssentiallySmall.{u + 1} Z.ProEt := ProEtale.VaryingRing.siteSmall Z
  let := abelianSheafify.{u + 1, u, u + 1} (ProEt.topology Z)
  let := locallyBijective.{u + 1, u, u + 1} (ProEt.topology Z)
  let RZ := ProEtale.StrictTower.coefficients (R n) Z
  let := SheafOfModules.isMonoidal_W_independentCoefficients RZ
  let := SheafOfModules.monoidalCategory RZ
  let t := ordinaryEvaluationTensor.{u + 1, u, u} (ProEt.topology Z)
    (ProEtale.VaryingRing.coefficients R Z)
    (ProEtale.VaryingRing.coefficientTransition R φ Z) n
    ((ProEtale.VaryingRing.extension R φ j).obj M) N
  let e : eZ.obj T ≅
      (ProEtale.StrictTower.moduleJ (R n) j).obj (eX.obj M) ⊗ eZ.obj N :=
    t ≪≫ MonoidalCategory.tensorIso ((asIso δ).app M).symm (Iso.refl _)
  obtain ⟨Q, ⟨i⟩⟩ := nativeFiniteTensor_mem_essImage l E j n (eX.obj M) (eZ.obj N)
  have hs : (ProEtale.StrictTower.moduleJ (R n) j).essImage (eZ.obj T) :=
    ⟨Q, ⟨i ≪≫ e.symm⟩⟩
  have : IsIso b.unit := ProEtale.StrictTower.openBetaModuleJUnit (R n) j
  let ff := b.fullyFaithfulLOfIsIsoUnit
  let : (ProEtale.StrictTower.moduleJ (R n) j).Full := ff.full
  let : (ProEtale.StrictTower.moduleJ (R n) j).Faithful := ff.faithful
  have : IsIso (b.counit.app (eZ.obj T)) := b.isIso_counit_app_iff_mem_essImage.mpr hs
  exact evaluatedCounit a b q T

end WeilConjectures.CoefSupportOpenTensor
