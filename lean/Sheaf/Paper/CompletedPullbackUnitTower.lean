/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q70
-/
module

public import Sheaf.Paper.CompleteCoefficientDatum
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Sheaf.CategoryTheory.DiagramSiteRealization
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Limits
public import Sheaf.Algebra.Homology.KFlat
public import Sheaf.Paper.CompletedPullbackAdjunction
public import Sheaf.Paper.ConstantCompletionEquivalence
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Sheaf.Paper.ProEtaleConstantReductionTower
import Sheaf.Paper.RingedTopoiTensorComparisonData
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
import Sheaf.Paper.RingedTopoiTensorComparisonConstruction
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitOfUniverses
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Paper.AdicCompletionReduction
import Sheaf.CategoryTheory.SheafPullbackForgetComparison
import Sheaf.CategoryTheory.ModuleInverseImageAdjunction

import Sheaf.Paper.CompletionMap
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
/-! # The completion unit and completed pullback on strict quotient towers

Source: smooth-purity blueprint, fix-lem-exchanges, Proof Steps 2 and 5;
Stacks Tags 099M and 099N (blueprint: lem-sf-cbc-completed-pullback-unit-tower).

The canonical small model of the original pro-etale site only enlarges its Hom
universe. Its topology and base-change functor are the published transports of
those on the original site. All coefficient rings are constant sheaves, with no
finiteness assumption on their underlying sets. Level n means exponent n+1.
The existing quotient presentation fixes every strict transition and its K-flat
computation; the existing reduction/pullback comparison fixes tensor reassociation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.AdicSites
namespace AlgebraicGeometry.Scheme.CompletedPullbackUnitTower

/-- The published small model, with precisely the original pro-etale topology.
Source: Stacks 09A5 (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def site (T : Scheme.{t}) : Site.{t + 1} where
  objects := proEtaleSiteModel T
  topology := proEtaleModelTopology T

/-- The canonical geometric inverse image on the published small models.
Source: Stacks 00VC and 099N (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def inverse {T' T : Scheme.{t}} (g : T' ⟶ T) :
    Sheaf (proEtaleModelTopology T) (Type (t + 1)) ⥤
      Sheaf (proEtaleModelTopology T') (Type (t + 1)) :=
  letI := proEtaleModelBaseChange_isContinuous g
  (proEtaleModelBaseChange g).sheafPullback (Type (t + 1))
    (proEtaleModelTopology T) (proEtaleModelTopology T')

/-- The corresponding sectionwise direct image on these same models.
Source: Stacks 00VC (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def direct {T' T : Scheme.{t}} (g : T' ⟶ T) :
    Sheaf (proEtaleModelTopology T') (Type (t + 1)) ⥤
      Sheaf (proEtaleModelTopology T) (Type (t + 1)) :=
  letI := proEtaleModelBaseChange_isContinuous g
  (proEtaleModelBaseChange g).sheafPushforwardContinuous (Type (t + 1))
    (proEtaleModelTopology T) (proEtaleModelTopology T')

/-- The defining geometric adjunction, rather than an arbitrary functor adjunction.
Source: Stacks 00VC (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def adjunction {T' T : Scheme.{t}} (g : T' ⟶ T) : inverse g ⊣ direct g :=
  letI := proEtaleModelBaseChange_isContinuous g
  (proEtaleModelBaseChange g).sheafAdjunctionContinuous (Type (t + 1))
    (proEtaleModelTopology T) (proEtaleModelTopology T')

/-- The geometric inverse image is left exact on the equivalent small model.
Source: Stacks 00VC (blueprint: lem-sf-cbc-completed-pullback-unit-tower).
Proof: scheme base change preserves finite limits on the pro-etale sites. The
AsSmall equivalences preserve those limits. The sheaf inverse image is left Kan
extension followed by left exact sheafification, so preserves finite limits. -/
@[instance]
theorem inverse_finiteLimits {T' T : Scheme.{t}} (g : T' ⟶ T) :
    PreservesFiniteLimits (inverse g) := by
  let : (AsSmall.down : proEtaleSiteModel T ⥤ T.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{t, t + 1, t + 1} (C := T.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up : T'.ProEt ⥤ proEtaleSiteModel T').IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{t, t + 1, t + 1} (C := T'.ProEt)).functor.IsEquivalence
  let : PreservesFiniteLimits (proEtaleModelBaseChange g) := by
    dsimp only [proEtaleModelBaseChange]
    infer_instance
  let : RepresentablyFlat (proEtaleModelBaseChange g) := flat_of_preservesFiniteLimits _
  let := proEtaleModelBaseChange_isContinuous g
  dsimp only [inverse]
  exact Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullbackOfRepresentablyFlat
    (proEtaleModelBaseChange g) (Type (t + 1))
    (proEtaleModelTopology T) (proEtaleModelTopology T')

/-- The ring-valued inverse image on the transported small pro-etale sites.  This is
the same left-Kan-extension/sheafification construction as `inverse`, with the
commutative-ring value category; it is the transported version of
`proEtaleSheafInverseImage` from `def-weil-proetale-inverse-image`.
Source: Stacks 00YV and 03D2 (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
noncomputable def transportedRingInverseImage {T' T : Scheme.{t}} (g : T' ⟶ T) :
    Sheaf (proEtaleModelTopology T) CommRingCat.{t + 1} ⥤
      Sheaf (proEtaleModelTopology T') CommRingCat.{t + 1} :=
  letI := proEtaleModelBaseChange_isContinuous g
  (proEtaleModelBaseChange g).sheafPullback (CommRingCat.{t + 1})
    (proEtaleModelTopology T) (proEtaleModelTopology T')

/-- The actual ring direct image on the small models.
Source: Stacks 00YV (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def transportedRingDirectImage {T' T : Scheme.{t}} (g : T' ⟶ T) :
    Sheaf (proEtaleModelTopology T') CommRingCat.{t + 1} ⥤
      Sheaf (proEtaleModelTopology T) CommRingCat.{t + 1} :=
  letI := proEtaleModelBaseChange_isContinuous g
  (proEtaleModelBaseChange g).sheafPushforwardContinuous CommRingCat.{t + 1}
    (proEtaleModelTopology T) (proEtaleModelTopology T')

/-- The ring adjunction unit, forgetting commutativity on the small models.
Source: Stacks 00YV and 03D2 (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def transportedRingUnit {T' T : Scheme.{t}} (g : T' ⟶ T)
    (O : Sheaf (proEtaleModelTopology T) CommRingCat.{t + 1}) :
    siteModuleRings O ⟶
      siteModuleRings ((transportedRingDirectImage g).obj
        ((transportedRingInverseImage g).obj O)) :=
  letI := proEtaleModelBaseChange_isContinuous g
  (sheafCompose (proEtaleModelTopology T) (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
    (((proEtaleModelBaseChange g).sheafAdjunctionContinuous CommRingCat.{t + 1}
      (proEtaleModelTopology T) (proEtaleModelTopology T')).unit.app O)

/-- Module inverse image along the actual transported ring unit, as in
`proEtaleModuleInverseImage`, already in the small-model coordinates.
Source: Stacks 03D2 (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def transportedModuleInverseImage {T' T : Scheme.{t}} (g : T' ⟶ T)
    (O : Sheaf (proEtaleModelTopology T) CommRingCat.{t + 1}) :
    ConstantCompletion.Mod O ⥤
      ConstantCompletion.Mod ((transportedRingInverseImage g).obj O) :=
  letI := proEtaleModelBaseChange_isContinuous g
  SheafOfModules.pullback.{t + 1} (F := proEtaleModelBaseChange g)
    (J := proEtaleModelTopology T) (K := proEtaleModelTopology T')
    (transportedRingUnit g O)

/-- Underlying ring comparison: the set-adjoint of the ring adjunction unit.
Source: Stacks 00YV (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def ringUnderlyingMap {T' T : Scheme.{t}} (g : T' ⟶ T)
    (O : Sheaf (proEtaleModelTopology T) CommRingCat.{t + 1}) :
    (inverse g).obj ((sheafCompose (proEtaleModelTopology T)
      (CategoryTheory.forget CommRingCat)).obj O) ⟶
      (sheafCompose (proEtaleModelTopology T') (CategoryTheory.forget CommRingCat)).obj
        ((transportedRingInverseImage g).obj O) :=
  letI := proEtaleModelBaseChange_isContinuous g
  ((adjunction g).homEquiv _ _).symm
    ((sheafCompose (proEtaleModelTopology T) (CategoryTheory.forget CommRingCat)).map
      (((proEtaleModelBaseChange g).sheafAdjunctionContinuous CommRingCat.{t + 1}
        (proEtaleModelTopology T) (proEtaleModelTopology T')).unit.app O))

/-- The canonical constant map, adjoint to sheafification of constant sections.
This is `proEtaleConstantInverseImageMap` on the small models, with unrestricted
coefficient universe, rather than a choice of an isomorphism of constant sheaves.
Source: Stacks 0H7J (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def constantInverseImageMap {T' T : Scheme.{t}} (g : T' ⟶ T)
    (B : CommRingCat.{t + 1}) :
    (transportedRingInverseImage g).obj
        ((constantSheaf (proEtaleModelTopology T) CommRingCat.{t + 1}).obj B) ⟶
      (constantSheaf (proEtaleModelTopology T') CommRingCat.{t + 1}).obj B :=
  letI := proEtaleModelBaseChange_isContinuous g
  (((proEtaleModelBaseChange g).sheafAdjunctionContinuous CommRingCat.{t + 1}
    (proEtaleModelTopology T) (proEtaleModelTopology T')).homEquiv _ _).symm
      (((sheafificationAdjunction (proEtaleModelTopology T) CommRingCat.{t + 1}).homEquiv
        _ _).symm
          (Functor.whiskerLeft (proEtaleModelBaseChange g).op
            (toSheafify (proEtaleModelTopology T')
              ((Functor.const (proEtaleSiteModel T')ᵒᵖ).obj B))))



private theorem modelFlat {T' T : Scheme.{t}} (g : T' ⟶ T) :
    RepresentablyFlat (proEtaleModelBaseChange g) := by
  let : (AsSmall.down : proEtaleSiteModel T ⥤ T.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{t, t + 1, t + 1} (C := T.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up : T'.ProEt ⥤ proEtaleSiteModel T').IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{t, t + 1, t + 1} (C := T'.ProEt)).functor.IsEquivalence
  let : PreservesFiniteLimits (proEtaleModelBaseChange g) := by
    dsimp only [proEtaleModelBaseChange]
    infer_instance
  exact flat_of_preservesFiniteLimits _

section AlgebraicLift

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {C D : Type u} [SmallCategory C] [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (F : C ⥤ D) [F.IsContinuous J K] [RepresentablyFlat F]

omit [RepresentablyFlat F] in
private theorem setPush_rightAdjoint :
    (F.sheafPushforwardContinuous (Type u) J K).IsRightAdjoint := inferInstance

omit [RepresentablyFlat F] in
private theorem ringPush_rightAdjoint :
    (F.sheafPushforwardContinuous CommRingCat.{u} J K).IsRightAdjoint := inferInstance

omit [RepresentablyFlat F] in
private theorem abelianPush_rightAdjoint :
    (F.sheafPushforwardContinuous AddCommGrpCat.{u} J K).IsRightAdjoint := inferInstance

-- Cache these Prop-valued instances to avoid repeated adjoint searches.
attribute [local instance] setPush_rightAdjoint ringPush_rightAdjoint abelianPush_rightAdjoint

private def ringUnit (O : Sheaf J CommRingCat.{u}) :
    siteModuleRings O ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj
      (siteModuleRings ((F.sheafPullback CommRingCat.{u} J K).obj O)) :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map
    ((F.sheafAdjunctionContinuous CommRingCat.{u} J K).unit.app O)

private def modulePull (O : Sheaf J CommRingCat.{u}) :
    ConstantCompletion.Mod O ⥤
      ConstantCompletion.Mod ((F.sheafPullback CommRingCat.{u} J K).obj O) :=
  SheafOfModules.pullback.{u} (F := F) (J := J) (K := K)
    (ringUnit J K F O)

private def ringMate (O : Sheaf J CommRingCat.{u}) :
    (F.sheafPullback (Type u) J K).obj
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj O) ⟶
      (sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj
        ((F.sheafPullback CommRingCat.{u} J K).obj O) :=
  ((F.sheafAdjunctionContinuous (Type u) J K).homEquiv _ _).symm
    ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map
      ((F.sheafAdjunctionContinuous CommRingCat.{u} J K).unit.app O))

set_option backward.isDefEq.respectTransparency false in
private theorem ringPresentation (O : Sheaf (J) CommRingCat.{u}) :
    ∃ p : SheafPullbackUnitPresentation (F := F)
        ((sheafCompose (J) (CategoryTheory.forget CommRingCat)).obj O)
        ((sheafCompose (K) (CategoryTheory.forget CommRingCat)).obj
          ((F.sheafPullback CommRingCat.{u} J K).obj O)),
      p.unit = (sheafCompose (J)
        (CategoryTheory.forget CommRingCat)).map
          ((F.sheafAdjunctionContinuous CommRingCat.{u}
            (J) (K)).unit.app O) := by
  let a := F.sheafAdjunctionContinuous CommRingCat.{u} J K
  let b := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F
    CommRingCat.{u} J K
  let e := a.leftAdjointUniq b
  let U := sheafCompose K (CategoryTheory.forget CommRingCat.{u})
  let c := sheafPullbackForgetIso J K F (CategoryTheory.forget CommRingCat.{u})
  let iso : U.obj ((F.sheafPullback CommRingCat.{u} J K).obj O) ≅
      (Functor.sheafPullbackConstruction.sheafPullback F (Type u) J K).obj
        ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj O) :=
    U.mapIso (e.app O) ≪≫ c.app O
  refine ⟨{ unit := ((sheafCompose J (CategoryTheory.forget CommRingCat.{u})).map
      (a.unit.app O)), iso := iso, equation := ?_ }, rfl⟩
  intro V r
  have he := Adjunction.unit_leftAdjointUniq_hom_app a b O
  have hc := sheafPullbackForgetIso_unit J K F
    (CategoryTheory.forget CommRingCat.{u}) O
  have he0 := congrArg (fun z ↦ z.hom.app V r) he
  have hc0 := congrArg (fun z ↦ z.hom.app V r) hc
  change (c.hom.app O).hom.app (F.op.obj V)
    ((e.hom.app O).hom.app (F.op.obj V) ((a.unit.app O).hom.app V r)) = _
  exact (congrArg (fun x ↦ (c.hom.app O).hom.app (F.op.obj V) x) he0).trans hc0

omit [RepresentablyFlat F] in
private theorem presentation_mate_isIso
    {S : Sheaf J (Type u)} {T : Sheaf K (Type u)}
    (p : SheafPullbackUnitPresentation (F := F) S T) :
    IsIso (((F.sheafAdjunctionContinuous (Type u) J K).homEquiv S T).symm p.unit) := by
  let a := F.sheafAdjunctionContinuous (Type u) J K
  let b := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F (Type u) J K
  let e := a.leftAdjointUniq b
  let q := e.app S ≪≫ p.iso.symm
  have hq : (a.homEquiv S T).symm p.unit = q.hom := by
    apply (a.homEquiv S T).injective
    rw [Equiv.apply_symm_apply]
    change p.unit = a.homEquiv S T ((e.app S).hom ≫ p.iso.inv)
    erw [Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app]
    have hp : p.unit ≫ (F.sheafPushforwardContinuous (Type u) J K).map p.iso.hom =
        b.unit.app S := by
      ext V r
      exact p.equation V r
    rw [← hp]
    simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id]
    rw [CategoryTheory.Functor.map_id, Category.comp_id]
  rw [hq]
  exact q.isIso_hom

private theorem ringUnderlyingMap_isIso (O : Sheaf J CommRingCat.{u}) :
    IsIso (ringMate J K F O) := by
  obtain ⟨p, hp⟩ := ringPresentation J K F O
  dsimp only [ringMate]
  rw [← hp]
  exact presentation_mate_isIso J K F p

private def moduleUnitMate (O : Sheaf (J) CommRingCat.{u})
    (M : ConstantCompletion.Mod O) :
    (F.sheafPullback (Type u) J K).obj ((ConstantCompletion.underlying O).obj M) ⟶
      (ConstantCompletion.underlying ((F.sheafPullback CommRingCat.{u} J K).obj O)).obj
        ((modulePull J K F O).obj M) :=
  ((F.sheafAdjunctionContinuous (Type u) J K).homEquiv _ _).symm
    ((ConstantCompletion.underlying O).map
      ((SheafOfModules.pullbackPushforwardAdjunction.{u}
        (F := F) (J := J)
        (K := K) (ringUnit J K F O)).unit.app M))

private theorem moduleUnitMate_isIso (O : Sheaf J CommRingCat.{u})
    (M : ConstantCompletion.Mod O) : IsIso (moduleUnitMate J K F O M) := by
  let a := F.sheafAdjunctionContinuous (Type u) J K
  let b := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F (Type u) J K
  let e := a.leftAdjointUniq b
  obtain ⟨p, hp⟩ := ringPresentation J K F O
  let : PreservesFiniteLimits (F.sheafPullback (Type u) J K) :=
    Functor.SmallCategories.instPreservesFiniteLimitsSheafSheafPullbackOfRepresentablyFlat
      F (Type u) J K
  let : PreservesFiniteLimits
      (Functor.sheafPullbackConstruction.sheafPullback F (Type u) J K) :=
    preservesFiniteLimits_of_natIso e
  obtain ⟨em, hem⟩ := SheafOfModules.inverseImage_underlying_of_ring_presentation
    (F := F) (J := J) (K := K) (ringUnit J K F O) p hp
  let c := sheafPullbackForgetIso J K F (CategoryTheory.forget AddCommGrpCat.{u})
  let ems := (sheafCompose K (CategoryTheory.forget AddCommGrpCat.{u})).mapIso (em.app M)
  let pr : SheafPullbackUnitPresentation (F := F)
      ((ConstantCompletion.underlying O).obj M)
      ((ConstantCompletion.underlying ((F.sheafPullback CommRingCat.{u} J K).obj O)).obj
        ((modulePull J K F O).obj M)) :=
    { unit := (ConstantCompletion.underlying O).map
        ((SheafOfModules.pullbackPushforwardAdjunction.{u} (F := F) (J := J) (K := K)
          (ringUnit J K F O)).unit.app M)
      iso := ems ≪≫ c.app ((SheafOfModules.toSheaf (siteModuleRings O)).obj M)
      equation := by
        intro V x
        have hm := congrArg (fun z ↦ z.hom.app V x) (hem M)
        have hc := congrArg (fun z ↦ z.hom.app V x)
          (sheafPullbackForgetIso_unit J K F
            (CategoryTheory.forget AddCommGrpCat.{u})
            ((SheafOfModules.toSheaf (siteModuleRings O)).obj M))
        exact (congrArg
          (fun z ↦ (c.hom.app ((SheafOfModules.toSheaf (siteModuleRings O)).obj M)).hom.app
            (F.op.obj V) z) hm).trans hc }
  exact presentation_mate_isIso J K F pr

set_option backward.isDefEq.respectTransparency false in
private def moduleUnderlyingIso (O : Sheaf (J) CommRingCat.{u}) :
    modulePull J K F O ⋙
        ConstantCompletion.underlying ((F.sheafPullback CommRingCat.{u} J K).obj O) ≅
      ConstantCompletion.underlying O ⋙ F.sheafPullback (Type u) J K := by
  let (M : ConstantCompletion.Mod O) : IsIso (moduleUnitMate J K F O M) :=
    moduleUnitMate_isIso J K F O M
  refine (NatIso.ofComponents (fun M ↦ asIso (moduleUnitMate J K F O M)) ?_).symm
  intro M N f
  change (F.sheafPullback (Type u) J K).map ((ConstantCompletion.underlying O).map f) ≫
      moduleUnitMate J K F O N = moduleUnitMate J K F O M ≫
        (ConstantCompletion.underlying ((F.sheafPullback CommRingCat.{u} J K).obj O)).map
          ((modulePull J K F O).map f)
  apply ((F.sheafAdjunctionContinuous (Type u) J K).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [moduleUnitMate, Equiv.apply_symm_apply]
  ext V x
  exact congrArg (fun z ↦ z.val.app V x)
    ((SheafOfModules.pullbackPushforwardAdjunction (F := F) (J := J) (K := K)
        (R := siteModuleRings ((F.sheafPullback CommRingCat.{u} J K).obj O))
        (ringUnit J K F O)).unit.naturality f)

private def binaryMap
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (X Y Z : Sheaf J (Type u))
    (op : ∀ V : Cᵒᵖ, X.obj.obj V → Y.obj.obj V → Z.obj.obj V)
    (hn : ∀ {V W : Cᵒᵖ} (f : V ⟶ W) x y,
      op W (X.obj.map f x) (Y.obj.map f y) = Z.obj.map f (op V x y))
    {H : Sheaf J (Type u)} (a : H ⟶ X) (b : H ⟶ Y) : H ⟶ Z :=
  ⟨{ app := fun V ↦ ↾fun x ↦ op V (a.hom.app V x) (b.hom.app V x)
     naturality := by
       intro V W f
       ext x
       change op W (a.hom.app W (H.obj.map f x)) (b.hom.app W (H.obj.map f x)) = _
       have ha := congrArg (fun q ↦ q x) (a.hom.naturality f)
       have hb := congrArg (fun q ↦ q x) (b.hom.naturality f)
       change a.hom.app W (H.obj.map f x) = X.obj.map f (a.hom.app V x) at ha
       change b.hom.app W (H.obj.map f x) = Y.obj.map f (b.hom.app V x) at hb
       rw [ha, hb]
       exact hn f _ _ }⟩

private theorem transport_binary
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (adj : L ⊣ F.sheafPushforwardContinuous (Type u) J K)
    {A B E : Sheaf J (Type u)} {A' B' E' : Sheaf K (Type u)}
    (eA : L.obj A ≅ A') (eB : L.obj B ≅ B') (eE : L.obj E ≅ E')
    (op : ∀ V : Cᵒᵖ, A.obj.obj V → B.obj.obj V → E.obj.obj V)
    (op' : ∀ V : Dᵒᵖ, A'.obj.obj V → B'.obj.obj V → E'.obj.obj V)
    (hn : ∀ {V W : Dᵒᵖ} (f : V ⟶ W) x y,
      op' W (A'.obj.map f x) (B'.obj.map f y) = E'.obj.map f (op' V x y))
    (hu : ∀ (V : Cᵒᵖ) x y,
      eE.hom.hom.app (F.op.obj V) ((adj.unit.app E).hom.app V (op V x y)) =
      op' (F.op.obj V)
        (eA.hom.hom.app (F.op.obj V) ((adj.unit.app A).hom.app V x))
        (eB.hom.hom.app (F.op.obj V) ((adj.unit.app B).hom.app V y)))
    (H : Sheaf J (Type u)) (a : H ⟶ A) (b : H ⟶ B) (z : H ⟶ E)
    (hz : ∀ V x, z.hom.app V x = op V (a.hom.app V x) (b.hom.app V x)) :
    ∀ V x, eE.hom.hom.app V ((L.map z).hom.app V x) =
      op' V (eA.hom.hom.app V ((L.map a).hom.app V x))
        (eB.hom.hom.app V ((L.map b).hom.app V x)) := by
  have hh : L.map z ≫ eE.hom =
      binaryMap A' B' E' op' hn (L.map a ≫ eA.hom) (L.map b ≫ eB.hom) := by
    apply (adj.homEquiv _ _).injective
    ext V x
    have ha := congrArg (fun q ↦ q.hom.app V x) (adj.unit.naturality a)
    have hb := congrArg (fun q ↦ q.hom.app V x) (adj.unit.naturality b)
    have hc := congrArg (fun q ↦ q.hom.app V x) (adj.unit.naturality z)
    change eE.hom.hom.app _ ((L.map z).hom.app _ ((adj.unit.app H).hom.app V x)) =
      op' _ (eA.hom.hom.app _ ((L.map a).hom.app _ ((adj.unit.app H).hom.app V x)))
        (eB.hom.hom.app _ ((L.map b).hom.app _ ((adj.unit.app H).hom.app V x)))
    change (adj.unit.app A).hom.app V (a.hom.app V x) =
      (L.map a).hom.app _ ((adj.unit.app H).hom.app V x) at ha
    change (adj.unit.app B).hom.app V (b.hom.app V x) =
      (L.map b).hom.app _ ((adj.unit.app H).hom.app V x) at hb
    change (adj.unit.app E).hom.app V (z.hom.app V x) =
      (L.map z).hom.app _ ((adj.unit.app H).hom.app V x) at hc
    rw [← ha, ← hb, ← hc, hz]
    exact hu V _ _
  intro V x
  exact congrArg (fun q ↦ q.hom.app V x) hh

set_option backward.isDefEq.respectTransparency false in
private def algebra (O : Sheaf (J) CommRingCat.{u}) :
    SheafOfModules.AlgebraicInverseImage (F.sheafPullback (Type u) J K) O
      ((F.sheafPullback CommRingCat.{u} J K).obj O) := by
  let := ringUnderlyingMap_isIso J K F O
  let eR := asIso (ringMate J K F O)
  let eM (M : ConstantCompletion.Mod O) := ((moduleUnderlyingIso J K F O).app M).symm
  let aR := F.sheafAdjunctionContinuous CommRingCat.{u}
    (J) (K)
  let aM := SheafOfModules.pullbackPushforwardAdjunction (F := F) (J := J) (K := K)
        (R := siteModuleRings ((F.sheafPullback CommRingCat.{u} J K).obj O))
        (ringUnit J K F O)
  have hr (V : Cᵒᵖ) (r : O.obj.obj V) :
      eR.hom.hom.app (F.op.obj V)
        (((F.sheafAdjunctionContinuous (Type u) J K).unit.app _).hom.app V r) =
          (aR.unit.app O).hom.app V r := by
    exact congrArg (fun z :
        (sheafCompose J (CategoryTheory.forget CommRingCat.{u})).obj O ⟶
          (F.sheafPushforwardContinuous (Type u) J K).obj
            ((sheafCompose K (CategoryTheory.forget CommRingCat.{u})).obj
              ((F.sheafPullback CommRingCat.{u} J K).obj O)) ↦ z.hom.app V r)
      (((F.sheafAdjunctionContinuous (Type u) J K).homEquiv _ _).apply_symm_apply
        ((sheafCompose (J) (CategoryTheory.forget CommRingCat)).map
          (aR.unit.app O)))
  have hm (M : ConstantCompletion.Mod O) (V : Cᵒᵖ)
      (m : M.val.obj V) :
      (eM M).hom.hom.app (F.op.obj V)
        (((F.sheafAdjunctionContinuous (Type u) J K).unit.app _).hom.app V m) =
          (aM.unit.app M).val.app V m := by
    exact congrArg (fun z : (ConstantCompletion.underlying O).obj M ⟶
        (F.sheafPushforwardContinuous (Type u) J K).obj
          ((ConstantCompletion.underlying
            ((F.sheafPullback CommRingCat.{u} J K).obj O)).obj
              ((modulePull J K F O).obj M)) ↦ z.hom.app V m)
      (((F.sheafAdjunctionContinuous (Type u) J K).homEquiv _ _).apply_symm_apply
        ((ConstantCompletion.underlying O).map (aM.unit.app M)))
  refine {
    ringUnderlying := eR
    modules := modulePull J K F O
    moduleUnderlying := moduleUnderlyingIso J K F O
    ringAdd := ?_
    ringMul := ?_
    ringZero := ?_
    ringOne := ?_
    moduleAdd := ?_
    moduleZero := ?_
    moduleSMul := ?_ }
  · intro H a b z hz
    exact transport_binary F (F.sheafPullback (Type u) J K)
      (F.sheafAdjunctionContinuous (Type u) J K) eR eR eR
      (fun V x y ↦ @Add.add (O.obj.obj V) inferInstance x y)
      (fun V x y ↦ @Add.add
        (((F.sheafPullback CommRingCat.{u} J K).obj O).obj.obj V) inferInstance x y)
      (fun f x y ↦
        (((F.sheafPullback CommRingCat.{u} J K).obj O).obj.map f).hom.map_add x y |>.symm)
      (by
        intro V x y
        erw [hr V _, hr V x, hr V y]
        exact ((aR.unit.app O).hom.app V).hom.map_add x y)
      H a b z hz
  · intro H a b z hz
    exact transport_binary F (F.sheafPullback (Type u) J K)
      (F.sheafAdjunctionContinuous (Type u) J K) eR eR eR
      (fun V x y ↦ @Mul.mul (O.obj.obj V) inferInstance x y)
      (fun V x y ↦ @Mul.mul
        (((F.sheafPullback CommRingCat.{u} J K).obj O).obj.obj V) inferInstance x y)
      (fun f x y ↦
        (((F.sheafPullback CommRingCat.{u} J K).obj O).obj.map f).hom.map_mul x y |>.symm)
      (by
        intro V x y
        erw [hr V _, hr V x, hr V y]
        exact ((aR.unit.app O).hom.app V).hom.map_mul x y)
      H a b z hz
  · intro H a ha
    exact transport_binary F (F.sheafPullback (Type u) J K)
      (F.sheafAdjunctionContinuous (Type u) J K) eR eR eR
      (fun V _ _ ↦ (0 : O.obj.obj V))
      (fun V _ _ ↦ (0 : ((F.sheafPullback CommRingCat.{u} J K).obj O).obj.obj V))
      (fun f _ _ ↦ (((F.sheafPullback CommRingCat.{u} J K).obj O).obj.map f).hom.map_zero |>.symm)
      (by
        intro V x y
        erw [hr V _]
        exact ((aR.unit.app O).hom.app V).hom.map_zero)
      H a a a ha
  · intro H a ha
    exact transport_binary F (F.sheafPullback (Type u) J K)
      (F.sheafAdjunctionContinuous (Type u) J K) eR eR eR
      (fun V _ _ ↦ (1 : O.obj.obj V))
      (fun V _ _ ↦ (1 : ((F.sheafPullback CommRingCat.{u} J K).obj O).obj.obj V))
      (fun f _ _ ↦ (((F.sheafPullback CommRingCat.{u} J K).obj O).obj.map f).hom.map_one |>.symm)
      (by
        intro V x y
        erw [hr V _]
        exact ((aR.unit.app O).hom.app V).hom.map_one)
      H a a a ha
  · intro M H a b z hz
    exact transport_binary F (F.sheafPullback (Type u) J K)
      (F.sheafAdjunctionContinuous (Type u) J K) (eM M) (eM M) (eM M)
      (fun V x y ↦ @Add.add (M.val.obj V) inferInstance x y)
      (fun V x y ↦ @Add.add (((modulePull J K F O).obj M).val.obj V) inferInstance x y)
      (fun f x y ↦ (((modulePull J K F O).obj M).val.map f).hom.map_add x y |>.symm)
      (by
        intro V x y
        erw [hm M V _, hm M V x, hm M V y]
        exact ((aM.unit.app M).val.app V).hom.map_add x y)
      H a b z hz
  · intro M H a ha
    exact transport_binary F (F.sheafPullback (Type u) J K)
      (F.sheafAdjunctionContinuous (Type u) J K) (eM M) (eM M) (eM M)
      (fun V _ _ ↦ (0 : M.val.obj V))
      (fun V _ _ ↦ (0 : ((modulePull J K F O).obj M).val.obj V))
      (fun f _ _ ↦ (((modulePull J K F O).obj M).val.map f).hom.map_zero |>.symm)
      (by
        intro V x y
        erw [hm M V _]
        exact ((aM.unit.app M).val.app V).hom.map_zero)
      H a a a ha
  · intro M H a b z hz
    exact transport_binary F (F.sheafPullback (Type u) J K)
      (F.sheafAdjunctionContinuous (Type u) J K) eR (eM M) (eM M)
      (fun V x y ↦ @SMul.smul (O.obj.obj V) (M.val.obj V) inferInstance x y)
      (fun V x y ↦ @SMul.smul
        (((F.sheafPullback CommRingCat.{u} J K).obj O).obj.obj V)
        (((modulePull J K F O).obj M).val.obj V) inferInstance x y)
      (fun f x y ↦ (((modulePull J K F O).obj M).val.map_smul f x y).symm)
      (by
        intro V x y
        erw [hm M V _, hr V x, hm M V y]
        exact ((aM.unit.app M).val.app V).hom.map_smul x y)
      H a b z hz

set_option backward.isDefEq.respectTransparency false in
private theorem algebra_naturality {R S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) :
    (F.sheafPullback (Type u) J K).map
        ((sheafCompose J (CategoryTheory.forget CommRingCat)).map φ) ≫
          (algebra J K F S).ringUnderlying.hom =
      (algebra J K F R).ringUnderlying.hom ≫
        (sheafCompose K (CategoryTheory.forget CommRingCat)).map
          ((F.sheafPullback CommRingCat.{u} J K).map φ) := by
  change _ ≫ ringMate J K F S = ringMate J K F R ≫ _
  apply ((F.sheafAdjunctionContinuous (Type u) J K).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  simp only [ringMate, Equiv.apply_symm_apply]
  ext V r
  exact congrArg (fun z ↦ z.hom.app V r)
    ((F.sheafAdjunctionContinuous CommRingCat.{u} J K).unit.naturality φ)



private def constantMap (B : CommRingCat.{u}) :
    (F.sheafPullback CommRingCat.{u} J K).obj
        ((constantSheaf J CommRingCat.{u}).obj B) ⟶
      (constantSheaf K CommRingCat.{u}).obj B :=
  ((F.sheafAdjunctionContinuous CommRingCat.{u} J K).homEquiv
    ((constantSheaf J CommRingCat.{u}).obj B)
    ((constantSheaf K CommRingCat.{u}).obj B)).symm
      (((sheafificationAdjunction J CommRingCat.{u}).homEquiv
        ((Functor.const Cᵒᵖ).obj B)
        ((F.sheafPushforwardContinuous CommRingCat.{u} J K).obj
          ((constantSheaf K CommRingCat.{u}).obj B))).symm
        (Functor.whiskerLeft F.op
          (toSheafify K ((Functor.const Dᵒᵖ).obj B))))

private def constants [HasFiniteLimits C] [PreservesFiniteLimits F] :
    constantSheaf J CommRingCat.{u} ⋙ F.sheafPullback CommRingCat.{u} J K ≅
      constantSheaf K CommRingCat.{u} :=
  let h := terminalIsTerminal (C := C)
  let a := ((constantSheafAdj J CommRingCat.{u} h).comp
    (F.sheafAdjunctionContinuous CommRingCat.{u} J K)).ofNatIsoRight
      (F.sheafPushforwardContinuousCompSheafSectionsObjIso CommRingCat.{u} J K (op (⊤_ C)))
  a.leftAdjointUniq (constantSheafAdj K CommRingCat.{u} (h.isTerminalObj F))

omit [RepresentablyFlat F] in
private theorem constants_hom [HasFiniteLimits C] [PreservesFiniteLimits F]
    (B : CommRingCat.{u}) : (constants J K F).hom.app B = constantMap J K F B := by
  symm
  let h := terminalIsTerminal (C := C)
  let aJ := constantSheafAdj J CommRingCat.{u} h
  let aK := constantSheafAdj K CommRingCat.{u} (h.isTerminalObj F)
  let aF := F.sheafAdjunctionContinuous CommRingCat.{u} J K
  let a := (aJ.comp aF).ofNatIsoRight
    (F.sheafPushforwardContinuousCompSheafSectionsObjIso CommRingCat.{u} J K (op (⊤_ C)))
  apply (a.homEquiv _ _).injective
  change a.homEquiv _ _ (constantMap J K F B) =
    a.homEquiv _ _ ((a.leftAdjointUniq aK).hom.app B)
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rw [Adjunction.homEquiv_ofNatIsoRight_apply]
  change (aJ.comp aF).homEquiv _ _ (constantMap J K F B) ≫ 𝟙 _ = _
  rw [Category.comp_id, Adjunction.comp_homEquiv]
  change aJ.homEquiv _ _ (aF.homEquiv _ _ ((aF.homEquiv _ _).symm _)) = _
  rw [Equiv.apply_symm_apply]
  change ((constantPresheafAdj CommRingCat.{u} h).comp
    (sheafificationAdjunction J CommRingCat.{u})).homEquiv _ _ _ = _
  rw [Adjunction.comp_homEquiv]
  change (constantPresheafAdj CommRingCat.{u} h).homEquiv _ _
    ((sheafificationAdjunction J CommRingCat.{u}).homEquiv _ _
      (((sheafificationAdjunction J CommRingCat.{u}).homEquiv _ _).symm _)) = _
  rw [Equiv.apply_symm_apply]
  change 𝟙 B ≫ _ = _
  rw [Category.id_comp]
  rfl


omit [RepresentablyFlat F] in
private theorem algebra_ext (O : Sheaf J CommRingCat.{u})
    (a b : SheafOfModules.AlgebraicInverseImage (F.sheafPullback (Type u) J K) O
      ((F.sheafPullback CommRingCat.{u} J K).obj O))
    (hr : a.ringUnderlying.hom = b.ringUnderlying.hom)
    (hm : a.modules = b.modules)
    (hu : ∀ M : ConstantCompletion.Mod O,
      HEq ((F.sheafAdjunctionContinuous (Type u) J K).homEquiv _ _
          (a.moduleUnderlying.inv.app M))
        ((F.sheafAdjunctionContinuous (Type u) J K).homEquiv _ _
          (b.moduleUnderlying.inv.app M))) : a = b := by
  rcases a with ⟨ar, aa, amu, az, ao, am, au, ma, mz, ms⟩
  rcases b with ⟨br, ba, bmu, bz, bo, bm, bu, na, nz, ns⟩
  dsimp only at hr hm hu
  cases hm
  have hR : ar = br := Iso.ext hr
  cases hR
  have hU : au = bu := by
    apply Iso.ext_inv
    apply NatTrans.ext
    funext M
    apply ((F.sheafAdjunctionContinuous (Type u) J K).homEquiv _ _).injective
    exact eq_of_heq (hu M)
  cases hU
  rfl

private def algebraicData [HasFiniteLimits C] [PreservesFiniteLimits F] :
    ConstantCompletion.InverseImageData (F.sheafPullback (Type u) J K) where
  rings := F.sheafPullback CommRingCat.{u} J K
  algebra := algebra J K F
  ring_naturality := algebra_naturality J K F
  constants := constants J K F

private def Normalized
    (E : ConstantCompletion.InverseImageData (F.sheafPullback (Type u) J K)) : Prop :=
  E.rings = F.sheafPullback CommRingCat.{u} J K ∧
    (∀ O : Sheaf J CommRingCat.{u},
      HEq (E.algebra O).ringUnderlying.hom (ringMate J K F O) ∧
      HEq (E.algebra O).modules (modulePull J K F O) ∧
      ∀ M : ConstantCompletion.Mod O,
        HEq ((F.sheafAdjunctionContinuous (Type u) J K).homEquiv _ _
            ((E.algebra O).moduleUnderlying.inv.app M))
          ((ConstantCompletion.underlying O).map
            ((SheafOfModules.pullbackPushforwardAdjunction.{u}
              (F := F) (J := J) (K := K) (ringUnit J K F O)).unit.app M))) ∧
    ∀ B : CommRingCat.{u}, HEq (E.constants.hom.app B) (constantMap J K F B)

private theorem algebraicData_normalized [HasFiniteLimits C] [PreservesFiniteLimits F] :
    Normalized J K F (algebraicData J K F) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro O
    refine ⟨HEq.rfl, HEq.rfl, ?_⟩
    intro M
    apply heq_of_eq
    exact ((F.sheafAdjunctionContinuous (Type u) J K).homEquiv _ _).apply_symm_apply _
  · intro B
    exact heq_of_eq (constants_hom J K F B)

private theorem normalized_unique [HasFiniteLimits C] [PreservesFiniteLimits F]
    (E : ConstantCompletion.InverseImageData (F.sheafPullback (Type u) J K))
    (hE : Normalized J K F E) : E = algebraicData J K F := by
  obtain ⟨hr, ha, hc⟩ := hE
  rcases E with ⟨rings, alg, hn, cs⟩
  dsimp only at hr ha hc
  subst rings
  have hA : alg = algebra J K F := by
    funext O
    apply algebra_ext J K F O
    · exact eq_of_heq (ha O).1
    · exact eq_of_heq (ha O).2.1
    · intro M
      exact ((ha O).2.2 M).trans
        ((algebraicData_normalized J K F).2.1 O |>.2.2 M).symm
  subst alg
  have hC : cs = constants J K F := by
    apply Iso.ext
    apply NatTrans.ext
    funext B
    exact (eq_of_heq (hc B)).trans (constants_hom J K F B).symm
  subst cs
  rfl

private theorem algebraicData_existsUnique [HasFiniteLimits C] [PreservesFiniteLimits F] :
    ∃! E : ConstantCompletion.InverseImageData (F.sheafPullback (Type u) J K),
      Normalized J K F E :=
  ⟨algebraicData J K F, algebraicData_normalized J K F,
    fun E hE ↦ normalized_unique J K F E hE⟩

end AlgebraicLift

/-- The unique algebraic lift with all data fields fixed by the actual ring and
module inverse images and their adjunction units. `HEq` only handles the dependent
codomains until the preceding equality of ring functors is substituted.
Source: Stacks 00YV, 03D2 and 0H7J
(blueprint: lem-sf-cbc-completed-pullback-unit-tower).
Proof: the set-adjoint of the ring unit is the canonical underlying-set comparison.
Finite-product preservation makes it invertible and preserves all ring-operation
graphs. Pullback along that unit is the module inverse image; the set-adjoint of
its unit is invertible and preserves addition, zero and the scalar-action graph.
These statements follow first on the Kan-extension generators, then after
sheafification. The canonical constant-section map is invertible and natural.
They assemble to InverseImageData with exactly the displayed data. Conversely the
predicate fixes the ring functor, the module functors, both underlying comparisons,
and the constant comparison componentwise. All remaining fields are propositions,
so extensionality and proof irrelevance give uniqueness. -/
theorem canonicalInverseImageData_existsUnique {T' T : Scheme.{t}} (g : T' ⟶ T) :
    letI := proEtaleModelBaseChange_isContinuous g
    ∃! F : ConstantCompletion.InverseImageData (inverse g),
      F.rings = transportedRingInverseImage g ∧
      (∀ O : Sheaf (proEtaleModelTopology T) CommRingCat.{t + 1},
        HEq (F.algebra O).ringUnderlying.hom (ringUnderlyingMap g O) ∧
        HEq (F.algebra O).modules (transportedModuleInverseImage g O) ∧
        ∀ M : ConstantCompletion.Mod O,
          HEq ((adjunction g).homEquiv _ _ ((F.algebra O).moduleUnderlying.inv.app M))
            ((ConstantCompletion.underlying O).map
              ((SheafOfModules.pullbackPushforwardAdjunction.{t + 1}
                (F := proEtaleModelBaseChange g) (J := proEtaleModelTopology T)
                (K := proEtaleModelTopology T')
                (R := siteModuleRings ((transportedRingInverseImage g).obj O))
                (transportedRingUnit g O)).unit.app M))) ∧
      ∀ B : CommRingCat.{t + 1},
        HEq (F.constants.hom.app B) (constantInverseImageMap g B) := by
  let := proEtaleModelBaseChange_isContinuous g
  let : (AsSmall.down : proEtaleSiteModel T ⥤ T.ProEt).IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{t, t + 1, t + 1} (C := T.ProEt)).inverse.IsEquivalence
  let : (AsSmall.up : T'.ProEt ⥤ proEtaleSiteModel T').IsEquivalence :=
    inferInstanceAs (AsSmall.equiv.{t, t + 1, t + 1} (C := T'.ProEt)).functor.IsEquivalence
  let : PreservesFiniteLimits (proEtaleModelBaseChange g) := by
    dsimp only [proEtaleModelBaseChange]
    infer_instance
  let : RepresentablyFlat (proEtaleModelBaseChange g) := modelFlat g
  exact algebraicData_existsUnique (proEtaleModelTopology T)
    (proEtaleModelTopology T') (proEtaleModelBaseChange g)

/-- The canonical algebraic inverse image, chosen from a predicate determining all
its data fields by actual pullbacks and unit-normalized comparisons.
Source: Stacks 00YV, 03D2 and 0H7J
(blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def canonicalInverseImageData {T' T : Scheme.{t}} (g : T' ⟶ T) :
    ConstantCompletion.InverseImageData (inverse g) :=
  (canonicalInverseImageData_existsUnique g).exists.choose

/-- The geometric morphism with its canonical algebraic lift, using the published
finite-product construction of ring and module inverse images.
Source: Stacks 00YV and 03D2 (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def morphism {T' T : Scheme.{t}} (g : T' ⟶ T) : Morphism (site T) (site T') where
  inverse := inverse g
  direct := direct g
  adjunction := adjunction g
  finiteLimits := inverse_finiteLimits g
  algebra := canonicalInverseImageData g

/-- Ordinary constant towers evaluated at any level are the identity functor.
Source: Stacks 0941 (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def diagonalEvaluation (S : Site.{u}) (A : Type u) [CommRing A] (n : ℕ) :
    S.delta A ⋙ S.evaluate A n ≅ 𝟭 (S.derived A) :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ by rfl)) ≪≫
    Functor.mapDerivedCategoryIdIso (S.modules A)

/-- The projection of the actual derived strict limit, obtained by evaluating the
constant/limit adjunction counit. On a K-injective tower it is the limit projection.
Source: Stacks 0941 (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def projection (S : Site.{u}) (A : Type u) [CommRing A]
    (M : S.towerDerived A) (n : ℕ) :
    (S.rlim A).obj M ⟶ (S.evaluate A n).obj M :=
  (diagonalEvaluation S A n).inv.app ((S.rlim A).obj M) ≫
    (S.evaluate A n).map ((S.deltaAdjunction A).counit.app M)

/-- The projection to the finite reduction, with its quotient action retained.
Source: Stacks 099M (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def finiteProjection (S : Site.{u}) (A : Type u) [CommRing A] (I : Ideal A)
    (N : S.derived A) (n : ℕ) :
    (S.completion A I).obj N ⟶
      (S.finiteRestriction A I n).obj ((S.finiteReduction A I n).obj N) :=
  projection S A ((S.reduction A I).obj N) n ≫
    (S.finiteEvaluationIso A I n).hom.app N

/-- The inverse reduced unit prescribed by clause (i): the scalar-extension adjunct
of the specified limit projection, before forgetting its finite coefficient action.
Source: Stacks 099M (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def finiteInverse (S : Site.{u}) (A : Type u) [CommRing A] (I : Ideal A)
    (N : S.derived A) (n : ℕ) :
    (S.finiteReduction A I n).obj ((S.completion A I).obj N) ⟶
      (S.finiteReduction A I n).obj N :=
  ((S.finiteAdjunction A I n).homEquiv _ _).symm (finiteProjection S A I N n)

/-- The finite coefficient target of the pulled-back strict quotient tower.
Source: Stacks 099N(5) (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def targetEvaluation {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (K : V.derived A) (n : ℕ) :
    (U.evaluate A n).obj ((f.towerPull A).obj ((V.reduction A I).obj K)) ≅
      (U.finiteRestriction A I n).obj
        ((f.pull (quotientRing A I n)).obj ((V.finiteReduction A I n).obj K)) :=
  (f.evaluatePullIso A n).app ((V.reduction A I).obj K) ≪≫
    (f.pull A).mapIso ((V.finiteEvaluationIso A I n).app K) ≪≫
      (f.finiteRestrictionPullIso A I n).app ((V.finiteReduction A I n).obj K)

/-- The constant-coefficient projection-induced alpha of corrected clause (iii).
It is the scalar-extension adjunct of the limit projection after R lim of tau,
exactly the constant-coefficient presentation in Stacks 099N(5).
Source: Stacks 099N(5) (blueprint: lem-sf-cbc-completed-pullback-unit-tower). -/
def finitePullbackProjection {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (K : V.derived A) (n : ℕ) :
    (U.finiteReduction A I n).obj ((U.completion A I).obj ((f.pull A).obj K)) ⟶
      (f.pull (quotientRing A I n)).obj ((V.finiteReduction A I n).obj K) :=
  ((U.finiteAdjunction A I n).homEquiv _ _).symm
    ((U.rlim A).map ((f.reductionPullIso A I).inv.app K) ≫
      projection U A ((f.towerPull A).obj ((V.reduction A I).obj K)) n ≫
        (targetEvaluation f A I K n).hom)

/-- Completion-unit reduction, strict tensor/pullback comparison, and the normalized
completed-pullback reduction, with no completeness assumption in (i) or (ii).

Source: smooth-purity blueprint, fix-lem-exchanges Proof Steps 2 and 5; Stacks
099M, 099N, 03EL, 06YS and 0G7E
(blueprint: lem-sf-cbc-completed-pullback-unit-tower).

Proof, following the node:
1. Represent N by one flat-term K-flat complex Q. On the diagram site the
   diagonal of Q is K-flat: tensor and acyclicity are levelwise. Thus the universal
   derived quotient presentation is represented by the strict tower Q tensor P_n.
2. Use the K-injective strict-limit model for C and its unit. The projection p_n
   satisfies p_n eta = u_n. Arbitrary-input adic-completion reduction makes its
   scalar-extension adjunct b_n invertible. Naturality of the scalar adjunction
   gives b_n F_n(eta)=1; hence b_n is the inverse of F_n(eta).
3. The cone of R(eta) evaluates to zero at every level. Kernels, cokernels and
   cohomology of strict towers are levelwise, so its representative is acyclic.
   Localization makes its cone zero, hence R(eta) invertible. Naturality of eta
   gives the natural strict inverse b, with evaluated inverse exactly b_n.
4. On Q the canonical tensor/pullback comparison commutes with each quotient
   transition, naturally in chain maps and chain homotopies. Pullback preserves
   flat-term K-flat representatives and quasi-isomorphisms. Localization of this
   resolving class descends the comparison, independently of Q. It is precisely
   the existing, representative-normalized reductionPullIso in inverse direction.
5. Compose this tau with b at Lg*K. This gives q as a natural isomorphism in the
   derived category of strict towers, so all its evaluated maps respect transitions.
6. For complete K, Stacks 099N(2),(5) and completedPullbackAdjunction express
   completed inverse image in constant-coefficient categories as C(Lg*K), with
   its R lim(tau) presentation. Naturality of the limit counit identifies its
   projection with tau_n p_n. Naturality of scalar extension makes tau_n b_n
   its adjunct, exactly finitePullbackProjection of corrected clause (iii).
   Its restriction of scalars is the component of the isomorphism q up to the
   finite comparison isomorphisms. Restriction of scalars detects
   quasi-isomorphisms, hence is conservative, so this finite-coefficient map is
   invertible, the last conjunct. No completed-ring coefficient arrow is
   identified here. -/
theorem completedPullbackUnitTower {T' T : Scheme.{t}} (g : T' ⟶ T)
    (A : Type (t + 1)) [CommRing A] (d : CompleteCoefficientDatum A) :
    ∃ b : (site T').completion A d.ideal ⋙ (site T').reduction A d.ideal ≅
        (site T').reduction A d.ideal,
      (∀ N : (site T').derived A,
        b.inv.app N = ((site T').reduction A d.ideal).map
          (((site T').unit A d.ideal).app N)) ∧
      (∀ (N : (site T').derived A) (n : ℕ),
        ((site T').evaluate A n).map (b.hom.app N) ≫
            ((site T').finiteEvaluationIso A d.ideal n).hom.app N =
          ((site T').finiteEvaluationIso A d.ideal n).hom.app
              (((site T').completion A d.ideal).obj N) ≫
            ((site T').finiteRestriction A d.ideal n).map
              (finiteInverse (site T') A d.ideal N n)) ∧
      ∃ q : (morphism g).pull A ⋙ (site T').completion A d.ideal ⋙
            (site T').reduction A d.ideal ≅
          (site T).reduction A d.ideal ⋙ (morphism g).towerPull A,
        (∀ K : (site T).derived A,
          q.hom.app K = b.hom.app (((morphism g).pull A).obj K) ≫
            ((morphism g).reductionPullIso A d.ideal).inv.app K) ∧
        ∀ K : (site T).derived A, (site T).IsComplete A d.ideal K → ∀ n : ℕ,
          ((site T').evaluate A n).map (q.hom.app K) ≫
              (targetEvaluation (morphism g) A d.ideal K n).hom =
            ((site T').finiteEvaluationIso A d.ideal n).hom.app
                (((site T').completion A d.ideal).obj (((morphism g).pull A).obj K)) ≫
              ((site T').finiteRestriction A d.ideal n).map
                (finitePullbackProjection (morphism g) A d.ideal K n) ∧
          IsIso (finitePullbackProjection (morphism g) A d.ideal K n) := by
  sorry

end AlgebraicGeometry.Scheme.CompletedPullbackUnitTower
