/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
public import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
public import Submission.WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Submission.WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Submission.WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Submission.WeilConjectures.CategoryTheory.LanContinuityFromRepresentables

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Sections of the etale to pro-etale comparison inverse image

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange,
Sections of the comparison inverse image (blueprint: lem-weil-pbc-comparison-sections).
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/- The following lemmas specialize the coefficient-independent proofs in
Comparison/FullyFaithful and Comparison/Continuity to sets. Filtered colimits of
sets commute with finite limits, so the same affine-basis sheaf argument applies. -/
open Scheme in
private theorem setLanRelative (S : Scheme.{u}) (F : S.Etaleᵒᵖ ⥤ (Type (u + 1))) :
    Functor.PreservesRelativeFilteredColimits.{u} (AffineEtale.toAffineProEt S)
      ((AffineProEt.toProEt S).op ⋙ (Scheme.toProEt S).op.lan.obj F) := by
  constructor
  intro I _ _ K c hc
  -- The limit cone in the pro-étale site.
  have hc₁ : IsLimit ((AffineProEt.toProEt S).mapCone c) := isLimitOfPreserves _ hc
  -- The limit cone in `Over S`, obtained by reflecting the `Scheme`-level limit cone
  -- along `Over.forget S`.
  have hcOver : IsLimit ((ProEt.forget S).mapCone ((AffineProEt.toProEt S).mapCone c)) :=
    isLimitOfReflects (CategoryTheory.Over.forget S)
      (((AffineProEt.isLimitMapConeToSchemeOfIsLimit c hc).ofIsoLimit
        (Functor.mapConeMapCone c).symm).ofIsoLimit (Functor.mapConeMapCone _).symm)
  -- The comparison of the two relevant diagrams in the pro-étale site.
  have e : (K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S ≅
      (K ⋙ AffineEtale.Spec S) ⋙ Scheme.toProEt S :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft K (AffineEtale.toAffineProEtCompToProEtIso S) ≪≫
      (Functor.associator _ _ _).symm
  -- Mapping into an étale `S`-scheme commutes with the cofiltered limit, by
  -- `Scheme.preservesColimit_yoneda`.
  have hpres : ∀ (X : S.Etaleᵒᵖ),
      PreservesColimit ((K ⋙ AffineEtale.Spec S).op ⋙ (Scheme.toProEt S).op)
        (coyoneda.obj (Opposite.op ((Scheme.toProEt S).op.obj X))) := by
    intro X
    have h₁ : ∀ {i j : I} (f : i ⟶ j), IsAffineHom
        ((((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S) ⋙
          ProEt.forget S).map f).left :=
      fun f ↦ inferInstanceAs
        (IsAffineHom ((AffineEtale.toAffineProEt S).map (K.map f)).left)
    have h₂ : ∀ (i : I), CompactSpace
        ((((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S) ⋙
          ProEt.forget S).obj i).left :=
      fun i ↦ inferInstanceAs (CompactSpace ((AffineEtale.toAffineProEt S).obj (K.obj i)).left)
    have h₃ : ∀ (i : I), QuasiSeparatedSpace
        ((((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S) ⋙
          ProEt.forget S).obj i).left :=
      fun i ↦ inferInstanceAs
        (QuasiSeparatedSpace ((AffineEtale.toAffineProEt S).obj (K.obj i)).left)
    have h₄ : LocallyOfFinitePresentation
        ((ProEt.forget S).obj ((Scheme.toProEt S).obj X.unop)).hom :=
      inferInstanceAs (LocallyOfFinitePresentation X.unop.hom)
    have := Scheme.preservesColimit_yoneda
      (((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S) ⋙ ProEt.forget S)
      ((ProEt.forget S).obj ((Scheme.toProEt S).obj X.unop))
    have hyon : IsColimit
        ((yoneda.obj ((ProEt.forget S).obj ((Scheme.toProEt S).obj X.unop))).mapCocone
          ((ProEt.forget S).mapCone ((AffineProEt.toProEt S).mapCone c)).op) :=
      isColimitOfPreserves _ hcOver.op
    have hy : IsColimit ((yoneda.obj ((Scheme.toProEt S).obj X.unop)).mapCocone
        ((AffineProEt.toProEt S).mapCone c).op) :=
      IsColimit.mapCoconeEquiv (ProEt.forgetOpCompYonedaIso ((Scheme.toProEt S).obj X.unop))
        (by exact hyon)
    have hco : IsColimit ((coyoneda.obj (Opposite.op ((Scheme.toProEt S).op.obj X))).mapCocone
        ((AffineProEt.toProEt S).mapCone c).op) :=
      IsColimit.mapCoconeEquiv (Coyoneda.objOpOp _).symm hy
    let : PreservesColimit ((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S).op
        (coyoneda.obj (Opposite.op ((Scheme.toProEt S).op.obj X))) :=
      preservesColimit_of_preserves_colimit_cocone hc₁.op hco
    exact preservesColimit_of_iso_diagram _ (NatIso.op e).symm
  let : PreservesColimit ((K ⋙ AffineEtale.Spec S).op ⋙ (Scheme.toProEt S).op)
      ((Scheme.toProEt S).op.leftKanExtension F) := inferInstance
  have e' : (K ⋙ AffineEtale.Spec S).op ⋙ (Scheme.toProEt S).op ≅
      ((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S).op := NatIso.op e
  let : PreservesColimit ((K ⋙ AffineEtale.toAffineProEt S) ⋙ AffineProEt.toProEt S).op
      ((Scheme.toProEt S).op.leftKanExtension F) :=
    preservesColimit_of_iso_diagram _ e'
  exact ⟨isColimitOfPreserves ((Scheme.toProEt S).op.leftKanExtension F) hc₁.op⟩

open Scheme in
private theorem setLanSheaf (S : Scheme.{u}) (F : S.Etaleᵒᵖ ⥤ (Type (u + 1)))
    (hF : Presheaf.IsSheaf (smallEtaleTopology S) F) :
    Presheaf.IsSheaf (AffineProEt.topology S)
      ((AffineProEt.toProEt S).op ⋙ (Scheme.toProEt S).op.lan.obj F) := by
  let := setLanRelative S F
  have : HasFilteredColimitsOfSize.{u, u} (Type (u + 1)) :=
    hasFilteredColimitsOfSize_of_univLE.{u, u, u + 1, u + 1}
  have : AB5OfSize.{u, u} (Type (u + 1)) := AB5OfSize_of_univLE.{u, u, u + 1, u + 1} (Type (u + 1))
  apply Presheaf.isSheaf_of_generates_of_isRelativelyPresentable
      (AffineEtale.toAffineProEt S) (AffineProEt.minimalPrecoverage S)
      (AffineEtale.topology S)
  · let iso : (AffineEtale.toAffineProEt S).op ⋙
        (AffineProEt.toProEt S).op ⋙ S.toProEt.op.lan.obj F ≅
        (AffineEtale.Spec S).op ⋙ F :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Functor.opComp _ _).symm _ ≪≫
        Functor.isoWhiskerRight (NatIso.op (AffineEtale.toAffineProEtCompToProEtIso S).symm) _ ≪≫
        Functor.isoWhiskerRight (Functor.opComp _ _) _ ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (asIso <| ((Scheme.toProEt S).op.lanUnit.app F)).symm
    rw [Presheaf.isSheaf_of_iso_iff iso]
    exact Functor.op_comp_isSheaf_of_isSheaf _ _ _ _ hF
  · exact AffineProEt.generates_minimalPrecoverage S
  · exact AffineProEt.minimalPrecoverage_le_relativelyPresentable S
  · exact AffineProEt.minimalPrecoverage_le_finite S


open Scheme in
private theorem setIsIsoToSheafify {S : Scheme.{u}}
    (F : Sheaf S.smallEtaleTopology (Type (u + 1))) (Y : S.ProEt) (hY : proAffineEtale Y.hom) :
    IsIso ((toSheafify (ProEt.topology S) ((toProEt S).op.lan.obj F.obj)).app (op Y)) := by
  have : HasLimitsOfSize.{u, u + 1} (Type (u + 1)) :=
    hasLimitsOfSizeShrink.{u, u + 1, u + 1, u + 1} (Type (u + 1))
  have h2 : IsIso ((AffineProEt.toProEt S).op.whiskerLeft
      (toSheafify (ProEt.topology S) ((toProEt S).op.lan.obj F.obj))) :=
    Functor.IsDenseSubsite.isIso_whiskerLeft_toSheafify
      (AffineProEt.topology S) _ _ (Type (u + 1)) _
      (setLanSheaf S F.obj F.property)
  exact inferInstanceAs (IsIso (((AffineProEt.toProEt S).op.whiskerLeft
    (toSheafify (ProEt.topology S) ((toProEt S).op.lan.obj F.obj))).app
      (op (AffineProEt.mk Y.hom hY))))

open Scheme in
private theorem setComparisonUnit (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    ((ProEtale.comparisonCoefficientAdjunction (Type (u + 1)) X).unit.app F).hom =
      (toProEt X).op.lanUnit.app F.obj ≫
        (toProEt X).op.whiskerLeft
          (toSheafify _ ((toProEt X).op.lan.obj F.obj)) := by
  change (sheafToPresheaf _ (Type (u + 1))).map
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous _ _ _ _).unit.app F) = _
  rw [Functor.sheafPullbackConstruction.sheafAdjunctionContinuous,
    Adjunction.map_restrictFullyFaithful_unit_app]
  simp

open Scheme in
private theorem setComparisonUnit_isIso (X : Scheme.{u})
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (W : X.Etale)
    [IsAffine W.left] :
    IsIso (((ProEtale.comparisonCoefficientAdjunction (Type (u + 1)) X).unit.app F).hom.app
      (op W)) := by
  rw [setComparisonUnit]
  have : IsIso ((toSheafify (ProEt.topology X) ((toProEt X).op.lan.obj F.obj)).app
      (op ((toProEt X).obj W))) :=
    setIsIsoToSheafify F ((toProEt X).obj W)
      (@proAffineEtale.of_isAffine _ _ (inferInstanceAs (IsAffine W.left)) W.hom
        (inferInstanceAs (Etale W.hom)))
  change IsIso (((toProEt X).op.lanUnit.app F.obj).app (op W) ≫
    (toSheafify (ProEt.topology X) ((toProEt X).op.lan.obj F.obj)).app
      (op ((toProEt X).obj W)))
  infer_instance

-- Localize the comparison adjunction at U, commute scheme base change with the
-- comparison direct image, and evaluate the resulting isomorphism at the terminal
-- object. The comparison unit there is invertible.


end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- Full faithfulness of the set-valued comparison, in its unit-normalized form.
Source: Bhatt--Scholze, Lemmas 5.1.1--5.1.2.
(auxiliary; not a blueprint node).

Proof: Restrict the unit to the dense affine etale subsite. At every affine etale
object the Kan-extension unit is invertible because the inclusion is fully faithful,
and the sheafification map is invertible by the affine section formula. Their
composite is the comparison unit. Restriction to the dense subsite and inclusion
of sheaves into presheaves both reflect isomorphisms. -/
theorem proEtaleComparisonUnitSets_isIso (X : Scheme.{u}) :
    IsIso (ProEtale.comparisonCoefficientAdjunction (Type (u + 1)) X).unit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  let R := (AffineEtale.Spec X).sheafPushforwardContinuous (Type (u + 1))
    (AffineEtale.topology X) X.smallEtaleTopology
  suffices IsIso ((R ⋙ sheafToPresheaf _ (Type (u + 1))).map
      ((ProEtale.comparisonCoefficientAdjunction (Type (u + 1)) X).unit.app F)) from
    isIso_of_reflects_iso _ (R ⋙ sheafToPresheaf _ (Type (u + 1)))
  change IsIso ((AffineEtale.Spec X).op.whiskerLeft
    ((ProEtale.comparisonCoefficientAdjunction (Type (u + 1)) X).unit.app F).hom)
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  have : IsAffine ((AffineEtale.Spec X).obj U.unop).left := by
    change IsAffine (Spec U.unop.left.unop)
    infer_instance
  exact setComparisonUnit_isIso X F ((AffineEtale.Spec X).obj U.unop)

private theorem isIso_app_of_colimits {C J : Type*} [Category* C] [Category* J]
    {P Q : Cᵒᵖ ⥤ Type (u + 1)} (a : P ⟶ Q) {K : J ⥤ C} (c : Cone K)
    (hP : IsColimit (P.mapCocone c.op)) (hQ : IsColimit (Q.mapCocone c.op))
    [∀ i, IsIso (a.app (op (K.obj i)))] : IsIso (a.app (op c.pt)) := by
  let e : K.op ⋙ P ≅ K.op ⋙ Q := NatIso.ofComponents
    (fun i ↦ asIso (a.app (op (K.obj i.unop))))
    (fun f ↦ a.naturality (K.map f.unop).op)
  let h := (IsColimit.precomposeHomEquiv e (Q.mapCocone c.op)).2 hQ
  have heq : a.app (op c.pt) = (hP.coconePointUniqueUpToIso h).hom := by
    apply hP.hom_ext
    intro i
    change P.map (c.π.app i.unop).op ≫ a.app (op c.pt) = _
    simp only [IsColimit.comp_coconePointUniqueUpToIso_hom]
    exact a.naturality (c.π.app i.unop).op
  rw [heq]
  infer_instance

private theorem setLanAffineContinuous (X : Scheme.{u})
    (G : X.Etaleᵒᵖ ⥤ Type (u + 1)) :
    PreservesFilteredColimitsOfSize.{u, u}
      ((AffineProEt.toProEt X).op ⋙ (toProEt X).op.lan.obj G) := by
  constructor
  intro J _ _
  constructor
  intro K
  constructor
  intro c hc
  let K' := K.leftOp ⋙ AffineProEt.toProEt X
  let c' := (AffineProEt.toProEt X).mapCone (coneLeftOpOfCocone c)
  have hc' : IsLimit c' := isLimitOfPreserves _ (isLimitConeLeftOpOfCocone K hc)
  have hcOver : IsLimit ((ProEt.forget X).mapCone c') :=
    isLimitOfReflects (CategoryTheory.Over.forget X)
      (((AffineProEt.isLimitMapConeToSchemeOfIsLimit
        (coneLeftOpOfCocone c) (isLimitConeLeftOpOfCocone K hc)).ofIsoLimit
        (Functor.mapConeMapCone (coneLeftOpOfCocone c)).symm).ofIsoLimit
          (Functor.mapConeMapCone c').symm)
  have hpres (Y : X.Etale) :
      PreservesColimit K'.op (uliftYoneda.{u + 1}.obj ((toProEt X).obj Y)) := by
    have h₁ : ∀ {i j : Jᵒᵖ} (f : i ⟶ j),
        IsAffineHom (((K' ⋙ ProEt.forget X).map f).left) := fun f ↦
      inferInstanceAs (IsAffineHom ((K.leftOp.map f).left))
    have h₂ : ∀ i : Jᵒᵖ, CompactSpace (((K' ⋙ ProEt.forget X).obj i).left) := fun i ↦
      inferInstanceAs (CompactSpace ((K.leftOp.obj i).left))
    have h₃ : ∀ i : Jᵒᵖ, QuasiSeparatedSpace (((K' ⋙ ProEt.forget X).obj i).left) := fun i ↦
      inferInstanceAs (QuasiSeparatedSpace ((K.leftOp.obj i).left))
    have h₄ : LocallyOfFinitePresentation ((ProEt.forget X).obj ((toProEt X).obj Y)).hom :=
      inferInstanceAs (LocallyOfFinitePresentation Y.hom)
    have := Scheme.preservesColimit_yoneda (K' ⋙ ProEt.forget X)
      ((ProEt.forget X).obj ((toProEt X).obj Y))
    have hyon : IsColimit
        ((yoneda.obj ((ProEt.forget X).obj ((toProEt X).obj Y))).mapCocone
          ((ProEt.forget X).mapCone c').op) := isColimitOfPreserves _ hcOver.op
    have hy : IsColimit ((yoneda.obj ((toProEt X).obj Y)).mapCocone c'.op) :=
      IsColimit.mapCoconeEquiv (ProEt.forgetOpCompYonedaIso ((toProEt X).obj Y))
        (by exact hyon)
    have : PreservesColimit K'.op (yoneda.obj ((toProEt X).obj Y)) :=
      preservesColimit_of_preserves_colimit_cocone hc'.op hy
    change PreservesColimit K'.op (yoneda.obj ((toProEt X).obj Y) ⋙ uliftFunctor.{u + 1})
    infer_instance
  have := lan_preserves_colimit_of_representables (toProEt X) G K'.op c'.op hc'.op hpres
  have hL := isColimitOfPreserves ((toProEt X).op.lan.obj G) hc'.op
  exact ⟨by exact hL.whiskerEquivalence (opOpEquivalence J).symm⟩

/-- The inverse image of an etale sheaf is continuous on affine ind-etale limits.
Source: Bhatt--Scholze, Lemmas 5.1.1--5.1.2, with the same finite-presentation
argument for arbitrary affine ind-etale stages.
(auxiliary; not a blueprint node).

Proof: Before sheafification the inverse image is a Kan extension. An etale
scheme is locally of finite presentation, so maps to it from a cofiltered limit
of affine schemes factor through a stage, with equality also detected at a
stage. Thus the representables defining the Kan extension preserve the given
filtered colimit. The density theorem and commutation of colimits imply that
the Kan extension does too. The affine section formula identifies this Kan
extension with its sheafification on every affine ind-etale stage and on the
limit; naturality identifies all restriction maps. -/
theorem proEtaleComparisonSets_continuous (X : Scheme.{u})
    (G : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    PreservesFilteredColimitsOfSize.{u, u}
      ((AffineProEt.toProEt X).op ⋙
        ((Functor.sheafPullbackConstruction.sheafPullback (toProEt X)
          (Type (u + 1)) X.smallEtaleTopology (ProEt.topology X)).obj G).obj) := by
  have := setLanAffineContinuous X G.obj
  constructor
  intro J _ _
  constructor
  intro K
  constructor
  intro c hc
  let K' := K.leftOp ⋙ AffineProEt.toProEt X
  let c' := (AffineProEt.toProEt X).mapCone (coneLeftOpOfCocone c)
  have hc' : IsLimit c' :=
    isLimitOfPreserves _ (isLimitConeLeftOpOfCocone K hc)
  have hL : IsColimit (((toProEt X).op.lan.obj G.obj).mapCocone c'.op) := by
    have h := isColimitOfPreserves
      ((AffineProEt.toProEt X).op ⋙ (toProEt X).op.lan.obj G.obj)
        (isLimitConeLeftOpOfCocone K hc).op
    exact h
  have hStages (j : Jᵒᵖᵒᵖ) : IsIso
      ((toSheafify (ProEt.topology X) ((toProEt X).op.lan.obj G.obj)).app (op (K'.obj j.unop))) :=
    setIsIsoToSheafify G _ (K.leftOp.obj j.unop).prop
  have hPoint : IsIso
      ((toSheafify (ProEt.topology X) ((toProEt X).op.lan.obj G.obj)).app (op c'.pt)) :=
    setIsIsoToSheafify G _ c.pt.unop.prop
  have h := @ProEtale.isColimitMapCoconeOfNatTrans _ _ _ _ _ _ _ _
    (toSheafify (ProEt.topology X) ((toProEt X).op.lan.obj G.obj)) _ c'.op
      hStages hPoint hL
  exact ⟨by exact h.whiskerEquivalence (opOpEquivalence J).symm⟩

/-- The comparison counit is invertible for a sheaf continuous on affine ind-etale
presentations.
Source: Bhatt--Scholze, Lemmas 5.1.1--5.1.2.
(auxiliary; not a blueprint node).

Proof: Test on the dense affine ind-etale subsite. Present each basis object by
an etale cofiltered diagram. Both the sheaf and its comparison inverse image carry
this limit to a colimit. On finite stages the counit is inverse to the comparison
unit, hence is invertible. The unique map between the two colimits is therefore
invertible, and its naturality identifies it with the counit at the limit object. -/
theorem proEtaleComparisonCounitSets_isIso_of_continuous (X : Scheme.{u})
    (F : Sheaf (ProEt.topology X) (Type (u + 1)))
    (hF : Functor.PreservesRelativeFilteredColimits.{u} (AffineEtale.toAffineProEt X)
      ((AffineProEt.toProEt X).op ⋙ F.obj)) :
    IsIso ((ProEtale.comparisonCoefficientAdjunction (Type (u + 1)) X).counit.app F) := by
  have hu := proEtaleComparisonUnitSets_isIso X
  let L := Functor.sheafPullbackConstruction.sheafPullback (toProEt X)
    (Type (u + 1)) X.smallEtaleTopology (ProEt.topology X)
  have : L.Full :=
    (ProEtale.comparisonCoefficientAdjunction (Type (u + 1)) X).full_L_of_isSplitEpi_unit_app
  have : L.Faithful :=
    (ProEtale.comparisonCoefficientAdjunction (Type (u + 1)) X).faithful_L_of_mono_unit_app
  let a := ((ProEtale.comparisonCoefficientAdjunction (Type (u + 1)) X).counit.app F).hom
  let R := (AffineProEt.toProEt X).sheafPushforwardContinuous (Type (u + 1))
    (AffineProEt.topology X) (ProEt.topology X)
  suffices IsIso ((R ⋙ sheafToPresheaf _ (Type (u + 1))).map
      ((ProEtale.comparisonCoefficientAdjunction (Type (u + 1)) X).counit.app F)) from
    isIso_of_reflects_iso _ (R ⋙ sheafToPresheaf _ (Type (u + 1)))
  change IsIso ((AffineProEt.toProEt X).op.whiskerLeft a)
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  obtain ⟨J, _, _, ⟨p⟩⟩ := U.unop.exists_relativeLimitPresentation
  let c := (AffineProEt.toProEt X).mapCone p.cone
  let K := p.diag ⋙ AffineEtale.Spec X
  let e : p.diag ⋙ AffineEtale.toAffineProEt X ⋙ AffineProEt.toProEt X ≅
      K ⋙ toProEt X := Functor.isoWhiskerLeft p.diag
        (AffineEtale.toAffineProEtCompToProEtIso X)
  let c' : Cone (K ⋙ toProEt X) := (Cone.postcompose e.hom).obj c
  have hcont := proEtaleComparisonSets_continuous X
    (((toProEt X).sheafPushforwardContinuous (Type (u + 1))
      X.smallEtaleTopology (ProEt.topology X)).obj F)
  have hP := isColimitOfPreserves
    ((AffineProEt.toProEt X).op ⋙
      (L.obj (((toProEt X).sheafPushforwardContinuous (Type (u + 1))
        X.smallEtaleTopology (ProEt.topology X)).obj F)).obj) p.isLimit.op
  obtain ⟨hQ⟩ := hF.nonempty_isColimit p.cone p.isLimit
  have hr : IsIso (((toProEt X).sheafPushforwardContinuous (Type (u + 1))
      X.smallEtaleTopology (ProEt.topology X)).map
        ((ProEtale.comparisonCoefficientAdjunction (Type (u + 1)) X).counit.app F)) := inferInstance
  have ha (j : J) : IsIso (a.app (op ((K ⋙ toProEt X).obj j))) := by
    exact NatIso.isIso_app_of_isIso
      ((((toProEt X).sheafPushforwardContinuous (Type (u + 1))
        X.smallEtaleTopology (ProEt.topology X)).map
          ((ProEtale.comparisonCoefficientAdjunction (Type (u + 1)) X).counit.app F)).hom)
        (op (K.obj j))
  exact isIso_app_of_colimits a c' (by exact hP) (by exact hQ)

end AlgebraicGeometry.Scheme
