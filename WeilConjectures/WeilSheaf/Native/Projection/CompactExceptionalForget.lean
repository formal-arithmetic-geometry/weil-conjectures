/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.CompactForgetComparison
public import WeilConjectures.WeilSheaf.Native.Projection.ProperExceptionalForget
public import WeilConjectures.WeilSheaf.Native.Projection.OpenExceptionalForget

/-! # The exceptional mate of the compact-support forget comparison -/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits Endofunctor
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.WeilComplex

open ProEtale

attribute [local instance] Compactification.over

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k₀))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The geometric adic compact direct image for the compactification defining the Weil one. -/
abbrev compactProjectionAdicShriek :=
  boundedConstructibleAdicLowerShriekOfCompactification (l := l)
    (ringChar_algebraicClosure_ne (k₀ := k₀) (l := l))
    (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
    (geometricFiberHomCompactification (k₀ := k₀) f)

/-- The compact-support forget comparison before the equivalence with condensed modules. -/
def compactProjectionAdicForgetIso :
    derivedLowerShriek k₀ l f ⋙ forgetBoundedConstructibleAdic k₀ l Y ≅
      forgetBoundedConstructibleAdic k₀ l X ⋙ compactProjectionAdicShriek k₀ l f :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    ((ProEtaleWeilSheaf.rightDerivedLowerShriekCompForgetIso k₀ l f
      (lowerShriekCompactification k₀ f)).app M.obj))
    (fun φ ↦ ObjectProperty.hom_ext _
      ((ProEtaleWeilSheaf.rightDerivedLowerShriekCompForgetIso k₀ l f
        (lowerShriekCompactification k₀ f)).hom.naturality φ.hom))

/-- The open and proper exceptional mates paste to the compact-support mate. -/
theorem isIso_mateEquiv_compactProjectionAdicForgetIso
    {R : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X}
    (adj : derivedLowerShriek k₀ l f ⊣ R)
    {R' : (DerivedCategory.boundedConstructibleAdic l
        (Y ↘ Spec (CommRingCat.of k₀)).geometricFiber).FullSubcategory ⥤
      (DerivedCategory.boundedConstructibleAdic l
        (X ↘ Spec (CommRingCat.of k₀)).geometricFiber).FullSubcategory}
    (adj' : compactProjectionAdicShriek k₀ l f ⊣ R') :
    IsIso (mateEquiv adj adj' (compactProjectionAdicForgetIso k₀ l f).inv).natTrans := by
  let c := nativeProjectionCompactification k₀ f
  let cb := geometricFiberHomCompactification (k₀ := k₀) f
  have : IsOpenImmersion c.i := c.isOpenImmersion
  have : IsProper c.g := c.isProper
  have : QuasiCompact c.i := c.quasiCompact_openImmersion inferInstance
  have : IsProper (Scheme.Hom.geometricFiberMap c.g (comp_over c.g
      (Spec (CommRingCat.of k₀)))) :=
    Scheme.Hom.geometricFiberMap_of_isStableUnderBaseChange (P := @IsProper) c.g _ ‹_›
  have : (derivedLowerStar (k₀ := k₀) (l := l) c.g).IsLeftAdjoint :=
    isLeftAdjoint_derivedLowerStar_of_isProper c.g
  have : (properProjectionAdicPush k₀ l c.g).IsLeftAdjoint :=
    isLeftAdjoint_boundedConstructibleAdicRightDerivedLowerStar_of_isProper k₀
      (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure
      (ringChar_algebraicClosure_ne (k₀ := k₀) (l := l)) _
  let ai := extensionByZeroUpperStarAdjunction (k₀ := k₀) (l := l) c.i
  let ag := Adjunction.ofIsLeftAdjoint (derivedLowerStar (k₀ := k₀) (l := l) c.g)
  let bi := boundedConstructibleAdicOpenImmersionLowerShriekUpperStarAdjunction (l := l) cb.i
  let bg := Adjunction.ofIsLeftAdjoint (properProjectionAdicPush k₀ l c.g)
  let α := (openProjectionAdicForgetIso k₀ l c.i).symm
  let β := (properProjectionAdicForgetIso k₀ l c.g).symm
  have : IsIso (mateEquiv ai bi α.hom).natTrans :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
      (fun M ↦ isIso_mateEquiv_openProjectionAdicForgetIso k₀ l c.i M)
  have : IsIso (mateEquiv ag bg β.hom).natTrans :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
      (fun M ↦ isIso_mateEquiv_properProjectionAdicForgetIso k₀ l c.g ag bg M)
  let e : derivedLowerShriek k₀ l f ≅ extensionByZero c.i ⋙ derivedLowerStar c.g :=
    NatIso.ofComponents (fun M ↦ Iso.refl _) (fun φ ↦ by
      simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
      rfl)
  have h := isIso_mateEquiv_vComp_whiskerLeft_whiskerRight ai bi ag bg adj adj'
    e (Iso.refl _) α.hom β.hom
  convert h using 1
  congr 1
  ext M
  apply ObjectProperty.hom_ext
  simp [compactProjectionAdicForgetIso, ProEtaleWeilSheaf.rightDerivedLowerShriekCompForgetIso,
    Adjunction.compForgetIso, openProjectionAdicForgetIso, properProjectionAdicForgetIso,
    α, β, e, TwoSquare.vComp, TwoSquare.whiskerLeft, TwoSquare.whiskerRight]

/-- The equivalence between the adic and condensed models on compact direct images. -/
def compactProjectionAdicCondensedIso :
    compactProjectionAdicShriek k₀ l f ⋙
        (boundedConstructibleAdicEquivBoundedConstructible l k₀
          (Over.mk (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure)).functor ≅
      (boundedConstructibleAdicEquivBoundedConstructible l k₀
          (Over.mk (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure)).functor ⋙
        CondensedRing.boundedConstructibleLowerShriekOfCompactification l
          (geometricFiberHomCompactification (k₀ := k₀) f) :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _
    ((adicRightDerivedLowerShriekOfCompactificationCompIso l _
      (geometricFiberHomCompactification (k₀ := k₀) f)).app M.obj))
    (fun φ ↦ ObjectProperty.hom_ext _
      ((adicRightDerivedLowerShriekOfCompactificationCompIso l _
        (geometricFiberHomCompactification (k₀ := k₀) f)).hom.naturality φ.hom))

/-- The same compact forget comparison has an invertible exceptional mate after passing to
the condensed model and to its chosen compactification. -/
theorem isIso_mateEquiv_compactProjectionForgetLowerShriekIso
    {R : WeilComplex k₀ l Y ⥤ WeilComplex k₀ l X}
    (adj : derivedLowerShriek k₀ l f ⊣ R) :
    IsIso (mateEquiv adj
      (CondensedRing.boundedConstructibleUpperShriekAdjunction l
        (geometricFiberHom (k₀ := k₀) f))
      (compactProjectionForgetLowerShriekIso k₀ l f).hom).natTrans := by
  let cb := geometricFiberHomCompactification (k₀ := k₀) f
  let EX := boundedConstructibleAdicEquivBoundedConstructible l k₀
    (Over.mk (X ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure)
  let EY := boundedConstructibleAdicEquivBoundedConstructible l k₀
    (Over.mk (Y ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure)
  let ac := CondensedRing.boundedConstructibleUpperShriekOfCompactificationAdjunction l cb
  let δ := compactProjectionAdicCondensedIso k₀ l f
  let aa := (EX.toAdjunction.comp (ac.comp EY.symm.toAdjunction)).ofNatIsoLeft
    δ.isoCompInverse.symm
  let β := (compactProjectionAdicForgetIso k₀ l f).symm
  have : IsIso (mateEquiv adj aa β.hom).natTrans :=
    isIso_mateEquiv_compactProjectionAdicForgetIso k₀ l f adj aa
  have : IsIso (mateEquiv aa ac δ.inv).natTrans :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun M ↦
      Adjunction.isIso_mateEquiv_app_of_isIso aa ac δ.symm
        EX.toAdjunction EY.toAdjunction M)
  have h := isIso_mateEquiv_isoHComp adj aa ac β δ.symm
  have hc : IsIso (mateEquiv adj ac
      (compactProjectionForgetLowerShriekOfCompactificationIso k₀ l f).inv).natTrans := by
    convert h using 1
    congr 1
    ext M
    apply ObjectProperty.hom_ext
    simp [compactProjectionForgetLowerShriekOfCompactificationIso,
      compactProjectionAdicCondensedIso, compactProjectionAdicForgetIso, Functor.isoHComp,
      CondensedRing.boundedConstructibleLowerShriekOfCompactificationCompatibility,
      ObjectProperty.liftCompιIso, β, δ]
  exact isIso_mateEquiv_whiskerLeftIso adj ac
    (CondensedRing.boundedConstructibleUpperShriekAdjunction l
      (geometricFiberHom (k₀ := k₀) f))
    (CondensedRing.boundedConstructibleLowerShriekOfCompactificationIso'_padicAlgCl l _ cb)
    (compactProjectionForgetLowerShriekOfCompactificationIso k₀ l f).symm

end AlgebraicGeometry.WeilComplex
