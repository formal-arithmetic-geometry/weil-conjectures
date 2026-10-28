/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import Sheaf.WeilSheaf.NativeExceptionalForgetfulData
import WeilConjectures.WeilSheaf.Localization
import Mathlib.CategoryTheory.EssentialImage
import Sheaf.WeilSheaf.NativeExceptionalClosureCompactSupport
import Sheaf.WeilSheaf.NativeExceptionalCompactSupportRealization

/-! # Canonical-model ordinary exceptional comparison

This isolates the comparison for the canonical family of forgetful models. The
main comparison theorem transports this result to arbitrary supplied models.
Source: current blueprint, cor-coef-verdier-weil-equivariance.proof.md,
exceptional-adjunction sentence, first comparison step.
(blueprint: lem-sf-native-exceptional-ordinary-counit-model-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.Endofunctor.IsoAlgebra
open WeilConjectures.AdicQbarRealization

namespace WeilConjectures.NativeExceptionalForgetful
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] [Fact (l ≠ D.p)]

private theorem underlying_constructible (T : Space D) (K : W D l T) :
    ProEtale.DerivedCategory.boundedAdicConstructible l (geometric D T).base.left
      (((WeilComplex.forget) ⋙
        (ProEtale.adicLowerStar l (closureMap D T)).rightDerivedFunctor).obj K) := by
  let e := (IsAlgClosure.equiv D.k₀ D.k (AlgebraicClosure D.k₀)).toRingEquiv
  let : IsIso (CommRingCat.ofHom e.toRingHom) := e.toCommRingCatIso.isIso_hom
  have : IsIso (closureMap D T) := by
    dsimp only [closureMap]
    infer_instance
  let V := WeilComplex.forget.obj K
  have hV := ((WeilComplex.forgetBoundedConstructibleAdic D.k₀ l T.base.left).obj K).property
  have hPull := ProEtale.bounded_homologyProperty_mapDerivedCategory_adicUpperStar
    (inv (closureMap D T)) hV.1 hV.2
  let push := ProEtale.adicLowerStar l (closureMap D T)
  let transport := push.rightDerivedFunctorIsoMapDerivedCategory.app V ≪≫
    (Functor.mapDerivedCategoryNatIso
      (ProEtale.adicUpperStarIsoLowerStarInv l (asIso (closureMap D T)).symm).symm).app V
  let : (ProEtale.DerivedCategory.boundedAdicConstructible l
      (geometric D T).base.left).IsClosedUnderIsomorphisms := by
    dsimp [ProEtale.DerivedCategory.boundedAdicConstructible]
    infer_instance
  exact (ProEtale.DerivedCategory.boundedAdicConstructible l
    (geometric D T).base.left).prop_of_iso transport.symm hPull

/-- The canonical forgetful-model comparison exists for every coefficient system.

Proof source: cor-coef-verdier-weil-equivariance.proof.md, final exceptional-
adjunction sentence. The native compactification and normalized open/proper and
scalar comparisons construct a canonical family of ForgetModels and its left
ordinary comparison. This is strictly the canonical-model part; transport to
arbitrary supplied ForgetModels is proved by the parent theorem.
(blueprint: lem-sf-native-exceptional-ordinary-counit-model-comparison). -/
theorem native_exceptional_ordinary_counit_model_comparison (R : Family l D) :
    ∃ model : ∀ T : Space D, ForgetModel D l R T,
      ∀ (X Y : Space D) (f₀ : X.base ⟶ Y.base)
        [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left]
        (S : CoefficientSystem D l f₀)
        (c : Compactification (geometricMap D f₀)),
      Nonempty (nativeShriek D l f₀ ⋙ (model Y).functor ≅
        (model X).functor ⋙ (S.ring.operation c .closed).F) := by
  classical
  let V (T : Space D) := WeilComplex.forget ⋙
    (ProEtale.adicLowerStar l (closureMap D T)).rightDerivedFunctor
  have ff (T : Space D) : (R.data (geometric D T)).realization.J.FullyFaithful :=
    Classical.choice ((Functor.FullyFaithful.nonempty_iff_map_bijective _).mpr
      (R.data (geometric D T)).realization.fully_faithful)
  let (T : Space D) := (ff T).full
  let (T : Space D) := (ff T).faithful
  have hV (T : Space D) (K : W D l T) :
      (R.data (geometric D T)).realization.J.essImage ((V T).obj K) :=
    ((R.data (geometric D T)).realization.image _).mp (underlying_constructible D l T K)
  let model (T : Space D) : ForgetModel D l R T :=
    { functor := Functor.essImage.liftFunctor (V T)
        (R.data (geometric D T)).realization.J (hV T)
      realization := Functor.isoWhiskerRight
        (Functor.essImage.liftFunctorCompIso _ _ (hV T))
        (sectionDerived l (geometric D T).base.left (R.data (geometric D T)).realization) }
  let q (T : Space D) :
      (model T).functor ⋙ (R.data (geometric D T)).realization.J ≅ V T :=
    Functor.essImage.liftFunctorCompIso _ _ (hV T)
  refine ⟨model, ?_⟩
  intro X Y f₀ _ _ _ S c
  let c₀ := HasCompactification.compactification f₀.left
    (hf := hasCompactification_of_over (k₀ := D.k₀) f₀.left)
  let a : nativeShriek D l f₀ ⋙ WeilComplex.forget ≅
      WeilComplex.forget ⋙
        NativeWeilOpenProper.ordinaryCompactSupport (k₀ := D.k₀) (l := l) f₀.left c₀ :=
    Functor.isoWhiskerLeft (WeilComplex.objectProperty D.k₀ l X.base.left).ι
      (NativeWeilOpenProper.compactificationComparison (k₀ := D.k₀) (l := l) f₀.left c₀)
  obtain ⟨b⟩ := native_exceptional_closure_compact_support D l X Y f₀ c₀ c
  obtain ⟨d⟩ := LocallyFiniteAdicCompactSupport.system_compact_support_realization
    l D (Fact.out : l ≠ D.p) (X := (geometric D X).base.left)
      (Y := (geometric D Y).base.left) (geometricMap D f₀)
      (R.data (geometric D X)).realization (R.data (geometric D Y)).realization S c
  let b' : WeilComplex.forget ⋙
      NativeWeilOpenProper.ordinaryCompactSupport (k₀ := D.k₀) (l := l) f₀.left c₀ ⋙
        (ProEtale.adicLowerStar l (closureMap D Y)).rightDerivedFunctor ≅
      V X ⋙ LocallyFiniteAdicCompactSupport.actual l c := by
    let e := Functor.isoWhiskerLeft
      (WeilComplex.forgetBoundedConstructibleAdic D.k₀ l X.base.left) b
    change _ ≅ V X ⋙ LocallyFiniteAdicCompactSupport.actual l c at e
    exact e
  apply Nonempty.intro
  apply (ff Y).whiskeringRight (W D l X) |>.preimageIso
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (q Y) ≪≫
    Functor.isoWhiskerRight a
      (ProEtale.adicLowerStar l (closureMap D Y)).rightDerivedFunctor ≪≫
    b' ≪≫ Functor.isoWhiskerRight (q X).symm _ ≪≫
    Functor.isoWhiskerLeft (model X).functor d.symm ≪≫
    (Functor.associator _ _ _).symm

end WeilConjectures.NativeExceptionalForgetful
