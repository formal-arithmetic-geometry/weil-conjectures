/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Reduction.FiniteReductionComparisons
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteSmoothPullbackExchange

/-! # Ordinary finite-reduction pullback coherence -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

attribute [local irreducible] Functor.mapDerivedCategory Scheme.sfIntrinsicModuleEquivalence

private theorem inverse_mate_shift
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ] [HasShift F ℤ]
    {G : C ⥤ D} {H : E ⥤ F} {L₁ : C ⥤ E} {R₁ : E ⥤ C}
    {L₂ : D ⥤ F} {R₂ : F ⥤ D}
    [G.CommShift ℤ] [H.CommShift ℤ] [L₁.CommShift ℤ] [R₁.CommShift ℤ]
    [L₂.CommShift ℤ] [R₂.CommShift ℤ]
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) [a.CommShift ℤ] [b.CommShift ℤ]
    (t : TwoSquare R₁ H G R₂) [NatTrans.CommShift t.natTrans ℤ] :
    NatTrans.CommShift ((mateEquiv a b).symm t).natTrans ℤ := by
  change NatTrans.CommShift
    ((Functor.leftUnitor _).inv ≫
      Functor.whiskerRight a.unit (G ⋙ L₂) ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (Functor.associator _ _ _).hom _ ≫
      Functor.whiskerRight (Functor.whiskerLeft L₁ t.natTrans) L₂ ≫
      Functor.whiskerRight (Functor.associator _ _ _).inv _ ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (L₁ ⋙ H) b.counit ≫
      (Functor.rightUnitor _).hom) ℤ
  infer_instance

private theorem rawModel_shift (P : PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    NatTrans.CommShift (P.finiteReductionRawPullbackModel f).hom ℤ := by
  let := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring X
  let := Scheme.sfIntrinsicModuleEquivalence_functor_additive P.Ring Y
  have he := eq_of_heq (P.finiteReductionPullbackPresentation f).choose_spec.1
  unfold finiteReductionRawPullbackModel
  rw [he]
  let U := ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f
  let EY := Scheme.sfIntrinsicModuleEquivalence Y P.Ring
  let EX := Scheme.sfIntrinsicModuleEquivalence X P.Ring
  let e := Functor.mapDerivedCategoryNatIso (Scheme.openSquarePullbackModel P.Ring f) ≪≫
    Functor.mapDerivedCategoryCompIso (EY.inverse ⋙ U) EX.functor ≪≫
      Functor.isoWhiskerRight (Functor.mapDerivedCategoryCompIso EY.inverse U)
        EX.functor.mapDerivedCategory ≪≫
        Functor.associator EY.inverse.mapDerivedCategory U.mapDerivedCategory
          EX.functor.mapDerivedCategory
  have hi : NatTrans.CommShift e.hom ℤ := by
    dsimp only [e, Iso.trans_hom, Functor.isoWhiskerRight_hom]
    infer_instance
  have he : e.hom =
      (Scheme.openSquareDerivedPullbackModel P.Ring f ≪≫
        P.finiteReductionPullbackPresentationNative f).hom := by
    ext K
    simp only [e, Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
      Category.comp_id]
    rfl
  rw [← he]
  exact hi

private def comparisonNatIso (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    P.finiteReductionPullback f ⋙ P.finiteReduction m hm hmn X ≅
      P.finiteReduction m hm hmn Y ⋙
        (P.finiteReductionSetting m hm).finiteReductionPullback f :=
  Functor.isoWhiskerRight (P.finiteReductionRawPullbackModel f).symm
      (P.finiteReduction m hm hmn X) ≪≫
    (Scheme.proEtaleReductionPullbackIso f
      (Scheme.proEtaleConstantRing Y P.Ring)
      (Scheme.proEtaleConstantRing Y (P.finiteReductionSetting m hm).Ring)
      (Scheme.proEtaleConstantRing X P.Ring)
      (Scheme.proEtaleConstantRing X (P.finiteReductionSetting m hm).Ring)
      (Scheme.proEtaleConstantRingMap (T := Y) (P.finiteReductionRingHom m hm hmn))
      (Scheme.proEtaleConstantRingMap (T := X) (P.finiteReductionRingHom m hm hmn))
      (Scheme.proEtaleConstantRingComparison f P.Ring)
      (Scheme.proEtaleConstantRingComparison f (P.finiteReductionSetting m hm).Ring)
      (P.finiteReductionCoefficientSquare m hm hmn f)).symm ≪≫
    Functor.isoWhiskerLeft (P.finiteReduction m hm hmn Y)
      ((P.finiteReductionSetting m hm).finiteReductionRawPullbackModel f)

private theorem comparison_commShift (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    NatTrans.CommShift (comparisonNatIso P m hm hmn f).hom ℤ := by
  let : (Scheme.proEtaleRingDerivedExtension
      (Scheme.proEtaleConstantRingMap (T := X)
        (P.finiteReductionRingHom m hm hmn))).CommShift ℤ :=
    inferInstanceAs ((P.finiteReduction m hm hmn X).CommShift ℤ)
  let : (Scheme.proEtaleRingDerivedExtension
      (Scheme.proEtaleConstantRingMap (T := Y)
        (P.finiteReductionRingHom m hm hmn))).CommShift ℤ :=
    inferInstanceAs ((P.finiteReduction m hm hmn Y).CommShift ℤ)
  let aY := P.finiteReductionAdjunction m hm hmn Y
  let aX := P.finiteReductionAdjunction m hm hmn X
  let : aY.CommShift ℤ := aY.commShift_of_rightAdjoint ℤ
  let : aX.CommShift ℤ := aX.commShift_of_rightAdjoint ℤ
  let b := Scheme.proEtaleRingRestrictionDerivedPullback f
    (Scheme.proEtaleConstantRing Y P.Ring)
    (Scheme.proEtaleConstantRing Y (P.finiteReductionSetting m hm).Ring)
    (Scheme.proEtaleConstantRing X P.Ring)
    (Scheme.proEtaleConstantRing X (P.finiteReductionSetting m hm).Ring)
    (Scheme.proEtaleConstantRingMap (T := Y) (P.finiteReductionRingHom m hm hmn))
    (Scheme.proEtaleConstantRingMap (T := X) (P.finiteReductionRingHom m hm hmn))
    (Scheme.proEtaleConstantRingComparison f P.Ring)
    (Scheme.proEtaleConstantRingComparison f (P.finiteReductionSetting m hm).Ring)
    (P.finiteReductionCoefficientSquare m hm hmn f)
  have hb : NatTrans.CommShift b.hom ℤ := by
    dsimp only [b, Scheme.proEtaleRingRestrictionDerivedPullback, Iso.trans_hom, Iso.symm_hom]
    infer_instance
  have hi := inverse_mate_shift aY aX (TwoSquare.mk _ _ _ _ b.inv)
  have ha := rawModel_shift P f
  have hc := rawModel_shift (P.finiteReductionSetting m hm) f
  dsimp only [comparisonNatIso, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom]
  have : NatTrans.CommShift
      (Scheme.proEtaleReductionPullbackIso f
        (Scheme.proEtaleConstantRing Y P.Ring)
        (Scheme.proEtaleConstantRing Y (P.finiteReductionSetting m hm).Ring)
        (Scheme.proEtaleConstantRing X P.Ring)
        (Scheme.proEtaleConstantRing X (P.finiteReductionSetting m hm).Ring)
        (Scheme.proEtaleConstantRingMap (T := Y) (P.finiteReductionRingHom m hm hmn))
        (Scheme.proEtaleConstantRingMap (T := X) (P.finiteReductionRingHom m hm hmn))
        (Scheme.proEtaleConstantRingComparison f P.Ring)
        (Scheme.proEtaleConstantRingComparison f (P.finiteReductionSetting m hm).Ring)
        (P.finiteReductionCoefficientSquare m hm hmn f)).inv ℤ := hi
  infer_instance

/-- The specified quotient/pullback comparison respects the specified integer shifts.
Source: blueprint finite-reduction-of-purity, Step 2; Stacks Tags 0D6D and 06YY.
(blueprint: lem-pur-finite-reduction-pullback-comparison-shift).

Proof: ordinary restriction of scalars and inverse image are exact, and their
commuting square is termwise compatible with every cochain shift. Localization
therefore makes the derived restriction square shift-compatible. Transpose its
inverse through the two extension/restriction adjunctions. The scalar-extension
shift is defined as the adjoint of the restriction shift, so shift compatibility
of units and counits proves shift compatibility of the inverse mate, which is
proEtaleReductionPullbackIso inverse. The ordinary raw-to-intrinsic pullback model
localizes an exact natural isomorphism. Its presentation comparison is the
composite of two exact-derived composition comparisons; hence it and its inverse
commute with shifts. Whisker the inverse mate by these model comparisons at the
two coefficient levels. Naturality and the composite-functor shift formula give
exactly the displayed component equation. Zero and negative shifts, zero objects,
identity ring maps and empty schemes require no separate assumption. -/
theorem finiteReduction_pullbackComparison_shift (P : PurityFiniteSetting.{u})
    (m : ℕ) (hm : 1 ≤ m) (hmn : m ≤ P.level)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (r : ℤ)
    (K : Scheme.proEtaleDerivedCategory Y P.Ring) :
    (P.finiteReduction m hm hmn X).map
        (((P.finiteReductionPullback f).commShiftIso r).hom.app K) ≫
      ((P.finiteReduction m hm hmn X).commShiftIso r).hom.app
        ((P.finiteReductionPullback f).obj K) ≫
      (P.finiteReductionPullbackComparison m hm hmn f K).hom⟦r⟧' =
    (P.finiteReductionPullbackComparison m hm hmn f (K⟦r⟧)).hom ≫
      ((P.finiteReductionSetting m hm).finiteReductionPullback f).map
        (((P.finiteReduction m hm hmn Y).commShiftIso r).hom.app K) ≫
      (((P.finiteReductionSetting m hm).finiteReductionPullback f).commShiftIso r).hom.app
        ((P.finiteReduction m hm hmn Y).obj K) := by
  have : NatTrans.CommShift (comparisonNatIso P m hm hmn f).hom ℤ :=
    comparison_commShift P m hm hmn f
  have he (L) : (comparisonNatIso P m hm hmn f).hom.app L =
      (P.finiteReductionPullbackComparison m hm hmn f L).hom := by rfl
  have h := NatTrans.shift_app_comm (comparisonNatIso P m hm hmn f).hom r K
  simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc, he] using h

end WeilConjectures.PurityFiniteSetting
