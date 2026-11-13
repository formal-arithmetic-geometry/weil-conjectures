/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTowerTraceCoefficients
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalDiagonalRightDerived
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceOrdinaryScalars
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceRestrictedPushAcyclic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective

/-! # Scalar restriction and direct-image comparisons for the diagonal trace -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u a v w wc
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

private theorem derivesOnKInjectives
    {A B : Type a} [Category.{v} A] [Category.{v} B]
    [Abelian A] [Abelian B] [HasDerivedCategory.{wc} B]
    (F : A ⥤ B) [F.Additive] :
    (CochainComplex.KInjectives.localizerMorphism A).Derives
      (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) := by
  intro I J f hf
  have : I.obj.IsKInjective := I.property
  have : J.obj.IsKInjective := J.property
  have : QuasiIso f.hom := hf
  obtain ⟨e, he⟩ := (CochainComplex.IsKInjective.quasiIso_iff f.hom).mp
    (inferInstance : QuasiIso f.hom)
  have : QuasiIso ((F.mapHomologicalComplex (.up ℤ)).map f.hom) := by
    rw [← he]
    exact (F.mapHomotopyEquiv e).quasiIso_hom
  change IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f.hom))
  infer_instance

private def squareOfAcyclic
    {A B C D : Type a} [Category.{v} A] [Category.{v} B]
    [Category.{v} C] [Category.{v} D] [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{wc} C] [HasDerivedCategory.{wc} D]
    [HasKInjectiveResolutions A]
    (F : A ⥤ B) (G : C ⥤ D) [F.Additive] [G.Additive]
    (U : A ⥤ C) (V : B ⥤ D) [U.Additive] [V.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (RF : DiagonalRightDerived F) (RG : DiagonalRightDerived G)
    (ordinary : F ⋙ V ≅ U ⋙ G)
    (hacyc : ∀ I : CochainComplex A ℤ, I.IsKInjective →
      IsIso (RG.η.app ((U.mapHomologicalComplex (.up ℤ)).obj I))) :
    ExactSquareOfUniverses F G U V RF RG ordinary := by
  let Fc := F.mapHomologicalComplex (.up ℤ)
  let Uc := U.mapHomologicalComplex (.up ℤ)
  let cc := NatIso.mapHomologicalComplex ordinary (.up ℤ)
  let etaL : (F ⋙ V).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (RF.R ⋙ V.mapDerivedCategory) :=
    Functor.whiskerLeft Fc V.mapDerivedCategoryFactors.inv ≫
      Functor.whiskerRight RF.η V.mapDerivedCategory
  let etaR : (F ⋙ V).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (U.mapDerivedCategory ⋙ RG.R) :=
    Functor.whiskerRight cc.hom DerivedCategory.Q ≫
      Functor.whiskerLeft Uc RG.η ≫
      Functor.whiskerRight U.mapDerivedCategoryFactors.inv RG.R
  have hL : (RF.R ⋙ V.mapDerivedCategory).IsRightDerivedFunctor etaL
      (HomologicalComplex.quasiIso A (.up ℤ)) := by
    apply (derivesOnKInjectives (F ⋙ V)).isRightDerivedFunctor_of_isIso etaL
    intro I
    have := RF.computation I.obj I.property
    change IsIso (V.mapDerivedCategoryFactors.inv.app (Fc.obj I.obj) ≫
      V.mapDerivedCategory.map (RF.η.app I.obj))
    infer_instance
  have hR : (U.mapDerivedCategory ⋙ RG.R).IsRightDerivedFunctor etaR
      (HomologicalComplex.quasiIso A (.up ℤ)) := by
    apply (derivesOnKInjectives (F ⋙ V)).isRightDerivedFunctor_of_isIso etaR
    intro I
    have := hacyc I.obj I.property
    change IsIso (DerivedCategory.Q.map (cc.hom.app I.obj) ≫
      RG.η.app (Uc.obj I.obj) ≫ RG.R.map (U.mapDerivedCategoryFactors.inv.app I.obj))
    infer_instance
  let e := Functor.rightDerivedUnique (RF.R ⋙ V.mapDerivedCategory)
    (U.mapDerivedCategory ⋙ RG.R) etaL etaR (HomologicalComplex.quasiIso A (.up ℤ))
  refine ⟨e, ?_⟩
  intro P
  have he := Functor.rightDerivedNatTrans_app (RF.R ⋙ V.mapDerivedCategory)
    (U.mapDerivedCategory ⋙ RG.R) etaL etaR
    (HomologicalComplex.quasiIso A (.up ℤ)) (Iso.refl _).hom P
  change etaL.app P ≫ e.hom.app (DerivedCategory.Q.obj P) = _ at he
  simp only [Iso.refl_hom, NatTrans.id_app, Category.id_comp] at he
  have h := congrArg (fun t ↦
    V.mapDerivedCategoryFactors.hom.app (Fc.obj P) ≫ t ≫
      RG.R.map (U.mapDerivedCategoryFactors.hom.app P)) he
  simp only [etaL, etaR, Fc, Uc, cc, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
    Iso.hom_inv_id_app_assoc, ← RG.R.map_comp, Iso.inv_hom_id_app] at h
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h

-- Preserve the published names of the existential section-normalization witnesses.
set_option linter.unusedVariables false in
/-- Scalar restrictions retain the coefficient cones and the normalized push squares.

Source: Stacks Tag 070G for K-injective derivation. -/
theorem exists_diagonalTraceScalarComparisons (l : ℕ) [Fact l.Prime]
    {X S : Scheme.{u}}
    [DiagonalTraceLocalizations l X] [DiagonalTraceLocalizations l S]
    (f : X ⟶ S) (b : SpTowerShriek.Base l (ULift.{u} (Padic l)))
    (g : SpTowerShriek.Geometry l (ULift.{u} (Padic l)) b f)
    (cS : Chern l (ULift.{u} (Padic l)) S)
    (cX : Chern l (ULift.{u} (Padic l)) X)
    (nS : cS.Normalized l (ULift.{u} (Padic l)))
    (nX : cX.Normalized l (ULift.{u} (Padic l)))
    (Rf : DiagonalRightDerived
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f))
    (Rt : DiagonalRightDerived (diagonalTraceSystemPush l f)) :
    let E := ULift.{u} (Padic l)
    letI : g.push.Additive := g.pushAdditive
    letI : HasKInjectiveResolutions (Systems X (Arings l E X)) := b.kinjective X
    ∃ (rS : Restriction l E S) (rX : Restriction l E X),
      letI : rS.F.Additive := rS.additive
      letI : rX.F.Additive := rX.additive
      letI : PreservesFiniteLimits rS.F := rS.limits
      letI : PreservesFiniteColimits rS.F := rS.colimits
      letI : PreservesFiniteLimits rX.F := rX.limits
      letI : PreservesFiniteColimits rX.F := rX.colimits
      Nonempty (Coefficients l E S cS rS) ∧
      Nonempty (Coefficients l E X cX rX) ∧
      ∃ Rc : DiagonalRightDerived (diagonalTracePush l f),
      ∃ varyingOrdinary : g.push ⋙ rS.F ≅ rX.F ⋙ diagonalTraceSystemPush l f,
      ∃ varying_sections : ∀ (M : Systems X (Arings l E X)) (n : ℕ) (U : S.ProEtᵒᵖ)
          (x : (((g.push ⋙ rS.F).obj M).obj (op n)).obj.obj U),
        HEq (((varyingOrdinary.hom.app M).app (op n)).hom.app U x) x,
      Nonempty (ExactSquareOfUniverses g.push (diagonalTraceSystemPush l f)
        rX.F rS.F (canonicalDiagonalRightDerived g.push) Rt varyingOrdinary) ∧
      ∃ completedOrdinary : diagonalTracePush l f ⋙ diagonalCompletedRestriction l S ≅
        diagonalCompletedRestriction l X ⋙
          lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f,
      ∃ completed_sections : ∀ (M : DiagonalCompleted l X) (U : S.ProEtᵒᵖ)
          (x : ((diagonalTracePush l f ⋙ diagonalCompletedRestriction l S).obj M).obj.obj U),
        HEq ((completedOrdinary.hom.app M).hom.app U x) x,
      Nonempty (ExactSquare (diagonalTracePush l f)
        (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f)
        (diagonalCompletedRestriction l X) (diagonalCompletedRestriction l S)
        Rc Rf completedOrdinary) := by
  let E := ULift.{u} (Padic l)
  let : g.push.Additive := g.pushAdditive
  let : HasKInjectiveResolutions (Systems X (Arings l E X)) := b.kinjective X
  obtain ⟨rS, rX, aS, aX, vo, hvo, co, hco⟩ :=
    exists_diagonalTraceOrdinaryScalars l f b g cS cX nS nX
  let := rS.additive
  let := rX.additive
  let := rS.limits
  let := rS.colimits
  let := rX.limits
  let := rX.colimits
  obtain ⟨hv, hc⟩ := diagonalTrace_restrictedPush_acyclic l f rX Rf Rt
  let varying := squareOfAcyclic g.push (diagonalTraceSystemPush l f)
    rX.F rS.F (canonicalDiagonalRightDerived g.push) Rt vo hv
  have hGroth : IsGrothendieckAbelian.{u + 1} (DiagonalCompleted l X) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutionsOfUniverses.{u + 1,
        u, u + 1}
      (Scheme.ProEt.topology X) (Scheme.purTwistZlCompletion X l)).1
  let := hGroth
  let Rc := canonicalDiagonalRightDerived (diagonalTracePush l f)
  let completed := squareOfAcyclic (diagonalTracePush l f)
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ_[l])) f)
    (diagonalCompletedRestriction l X) (diagonalCompletedRestriction l S)
    Rc Rf co hc
  exact ⟨rS, rX, aS, aX, Rc, vo, hvo, ⟨varying⟩, co, hco,
    ⟨⟨completed.iso, completed.normalization⟩⟩⟩

end AlgebraicGeometry.ProEtale.DiagonalTrace
