/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NV
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs
public import Sheaf.AlgebraicGeometry.ContinuousCoefficientUniverse
public import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
public import Sheaf.NumberTheory.Padics.CoefficientExtension
public import Sheaf.AlgebraicGeometry.LocallyClosedStratification
public import Mathlib.Topology.NoetherianSpace

import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import all Sheaf.Paper.ProEtalePointComponentsMaps
import Sheaf.Paper.ProEtaleSheafificationWcontractibleSections
import WeilConjectures.CategoryTheory.Sites.MonObj
import Sheaf.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-!
# Local triviality over continuous p-adic field coefficients

Source: Hemo--Richarz--Scholbach, Example 3.1, and the agent rank/descent argument
recorded in (blueprint: lem-weil-pbc-condensed-lfp-local-triviality).
-/

@[expose] public section

universe u v w

open CategoryTheory MonoidalCategory Limits

open scoped CategoryTheory.Obj

namespace CategoryTheory
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
    (F : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [F.IsContinuous J K]
    [HasSheafify J AddCommGrpCat.{w}] [HasSheafify K AddCommGrpCat.{w}]
    [(J.W (A := AddCommGrpCat.{w})).IsMonoidal]
    [(K.W (A := AddCommGrpCat.{w})).IsMonoidal]
    [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
    [K.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w})]
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory

private lemma pushforwardRingMonObj (R : Sheaf K RingCat.{w}) :
    (Sheaf.monObj_sheafCompose_obj J
      ((F.sheafPushforwardContinuous RingCat.{w} J K).obj R)) =
    (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).monObjObj
      ((sheafCompose K (forget₂ RingCat.{w} AddCommGrpCat.{w})).obj R) := by
  apply MonObj.ext
  apply Sheaf.tensor_hom_ext
  change Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{w}) _ _ ≫ _ = _
  rw [Sheaf.μ_comp_map_mul]
  change _ = Functor.LaxMonoidal.μ (sheafToPresheaf J AddCommGrpCat.{w}) _ _ ≫
    (sheafToPresheaf J AddCommGrpCat.{w}).map
      (Functor.LaxMonoidal.μ (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K) _ _ ≫
        (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map
          (MonObj.mul (X := (sheafCompose K
            (forget₂ RingCat.{w} AddCommGrpCat.{w})).obj R)))
  rw [Functor.map_comp, ← Category.assoc,
    Functor.μ_sheafToPresheaf_comp_map_μ_sheafPushforwardContinuous]
  apply NatTrans.ext
  funext U
  let : MonObj ((sheafCompose K (forget₂ RingCat.{w} AddCommGrpCat.{w})).obj R).obj :=
    R.obj.monObjCompForget₂
  have h := congr_app (Sheaf.μ_comp_map_mul
    ((sheafCompose K (forget₂ RingCat.{w} AddCommGrpCat.{w})).obj R)) (F.op.obj U)
  simp only [NatTrans.comp_app] at h ⊢
  change _ = 𝟙 _ ≫
    (Functor.LaxMonoidal.μ (sheafToPresheaf K AddCommGrpCat.{w}) _ _).app (F.op.obj U) ≫
      (MonObj.mul (X := (sheafCompose K
        (forget₂ RingCat.{w} AddCommGrpCat.{w})).obj R)).hom.app (F.op.obj U)
  rw [Category.id_comp]
  erw [← h]
  rfl
end CategoryTheory


namespace AlgebraicGeometry.ProEtale

/-- Projection |X[S]| → S, using Spec LC(S,Z) = S × Spec Z and base change.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: lem-weil-pbc-condensed-lfp-local-triviality). -/
noncomputable def profiniteTestProjection (X : Scheme.{u}) (S : Profinite.{u}) :
    C(((profiniteToProEtOf X).obj S).left, S) :=
  (ContinuousMap.fst.comp
    ⟨(LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm,
      (LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm.continuous⟩).comp
      (Limits.pullback.fst (toSpecZ (profiniteToScheme.obj S)) (toSpecZ X)).base.hom

private noncomputable def absoluteProjection (S : Profinite.{u}) : C(profiniteToScheme.obj S, S) :=
  ContinuousMap.fst.comp
    ⟨(LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm,
      (LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).symm.continuous⟩
private lemma absoluteProjection_natural {S T : Profinite.{u}} (f : S ⟶ T) :
    (absoluteProjection T).comp (profiniteToScheme.map f).base.hom =
      f.hom.hom.comp (absoluteProjection S) := by
  ext p
  obtain ⟨⟨s, q⟩, rfl⟩ :=
    (LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)).surjective p
  simp only [ContinuousMap.comp_apply, absoluteProjection, ContinuousMap.fst_apply,
    ContinuousMap.coe_mk, Homeomorph.symm_apply_apply]
  change ((LocallyConstant.homeomorphPrimeSpectrum (T := T) (R := ℤ)).symm
      (PrimeSpectrum.comap _ (LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ)
        (s, q)))).1 = f s
  have h : PrimeSpectrum.comap (LocallyConstant.comapRingHom f.hom.hom)
      (LocallyConstant.homeomorphPrimeSpectrum (T := S) (R := ℤ) (s, q)) =
      LocallyConstant.homeomorphPrimeSpectrum (T := T) (R := ℤ) (f s, q) := by
    ext g
    rfl
  erw [h]
  exact congrArg Prod.fst
    ((LocallyConstant.homeomorphPrimeSpectrum (T := T) (R := ℤ)).symm_apply_apply (f s, q))
private lemma profiniteTestProjection_natural (X : Scheme.{u}) {S T : Profinite.{u}} (f : S ⟶ T) :
    (profiniteTestProjection X T).comp ((profiniteToProEtOf X).map f).left.base.hom =
      f.hom.hom.comp (profiniteTestProjection X S) := by
  change ((absoluteProjection T).comp
      (pullback.fst (toSpecZ (profiniteToScheme.obj T)) (toSpecZ X)).base.hom).comp
      ((profiniteToProEtOf X).map f).left.base.hom = _
  rw [ContinuousMap.comp_assoc]
  have h : ((profiniteToProEtOf X).map f).left ≫
      pullback.fst (toSpecZ (profiniteToScheme.obj T)) (toSpecZ X) =
      pullback.fst (toSpecZ (profiniteToScheme.obj S)) (toSpecZ X) ≫ profiniteToScheme.map f := by
    dsimp [profiniteToProEtOf, MorphismProperty.Over.pullback]
    exact pullback.lift_fst _ _ _
  have h' := congrArg (fun g ↦ g.base.hom) h
  change _ = f.hom.hom.comp ((absoluteProjection S).comp
    (pullback.fst (toSpecZ (profiniteToScheme.obj S)) (toSpecZ X)).base.hom)
  change (absoluteProjection T).comp
      ((pullback.fst (toSpecZ (profiniteToScheme.obj T)) (toSpecZ X)).base.hom.comp
        ((profiniteToProEtOf X).map f).left.base.hom) = _
  change (pullback.fst (toSpecZ (profiniteToScheme.obj T)) (toSpecZ X)).base.hom.comp
      ((profiniteToProEtOf X).map f).left.base.hom =
    (profiniteToScheme.map f).base.hom.comp
      (pullback.fst (toSpecZ (profiniteToScheme.obj S)) (toSpecZ X)).base.hom at h'
  erw [h']
  exact congrArg (fun g : C(profiniteToScheme.obj S, T) ↦
    g.comp (pullback.fst (toSpecZ (profiniteToScheme.obj S)) (toSpecZ X)).base.hom)
      (absoluteProjection_natural f)

private noncomputable def comparisonAdjoint (X : Scheme.{u}) (E : Type u)
    [NormedField E] : Profinite.continuousCoefficientRingObj E ⟶
      (pointLowerStar.obj ((lowerStar AddCommGrpCat.{u + 1} (toSpecZ X)).obj
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
            (continuousCoefficientRingSheaf X E)))) :=
  ⟨{ app := fun S ↦ AddCommGrpCat.ofHom
        { toFun := fun f ↦ ULift.up (f.down.comp (profiniteTestProjection X S.unop))
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
     naturality := by
       intro S T f
       apply ConcreteCategory.hom_ext
       intro g
       apply ULift.ext
       change (g.down.comp f.unop.hom.hom).comp (profiniteTestProjection X T.unop) =
         (g.down.comp (profiniteTestProjection X S.unop)).comp
           ((profiniteToProEtOf X).map f.unop).left.base.hom
       simp only [ContinuousMap.comp_assoc]
       erw [profiniteTestProjection_natural] }⟩

private noncomputable def comparison (X : Scheme.{u}) (E : Type u) [NormedField E] :
    condensedRingObj (Profinite.continuousCoefficientRingObj E) X ⟶
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
          (continuousCoefficientRingSheaf X E)) :=
  ((pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))).homEquiv _ _).symm
      (comparisonAdjoint X E)

private lemma comparison_eq (X : Scheme.{u}) (E : Type u) [NormedField E]
    (S : Profinite.{u}) (f : C(S, E)) :
    (((pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))).homEquiv _ _
        (comparison X E)).hom.app (Opposite.op S)) (ULift.up f) =
          ULift.up (f.comp (profiniteTestProjection X S)) := by
  rw [comparison, Equiv.apply_symm_apply]
  rfl

private noncomputable def comparisonAdjointRing (X : Scheme.{u}) (E : Type u) [NormedField E] :
    Profinite.continuousCoefficientRingSheaf E ⟶
      (profiniteToProEt.sheafPushforwardContinuous RingCat.{u + 1}
        (coherentTopology Profinite.{u}) (Scheme.ProEt.topology specZ)).obj
        (((MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)).sheafPushforwardContinuous
          RingCat.{u + 1} (Scheme.ProEt.topology specZ) (Scheme.ProEt.topology X)).obj
            (continuousCoefficientRingSheaf X E)) :=
  ⟨{ app := fun S ↦ RingCat.ofHom
        (ULift.ringEquiv.symm.toRingHom.comp
          (((ContinuousMap.compRightAlgHom ℤ E (profiniteTestProjection X S.unop)).toRingHom).comp
            ULift.ringEquiv.toRingHom))
     naturality := by
       intro S T f
       apply ConcreteCategory.hom_ext
       intro g
       apply ULift.ext
       change (g.down.comp f.unop.hom.hom).comp (profiniteTestProjection X T.unop) =
         (g.down.comp (profiniteTestProjection X S.unop)).comp
           ((profiniteToProEtOf X).map f.unop).left.base.hom
       simp only [ContinuousMap.comp_assoc]
       erw [profiniteTestProjection_natural] }⟩


private lemma comparisonAdjoint_isMonHom (X : Scheme.{u}) (E : Type u) [NormedField E] :
    IsMonHom (comparisonAdjoint X E) := by
  let F := MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)
  let J := coherentTopology Profinite.{u}
  let K := Scheme.ProEt.topology specZ.{u}
  let L := Scheme.ProEt.topology X
  let R := continuousCoefficientRingSheaf X E
  have h₁ := pushforwardRingMonObj F K L R
  have h₂ := pushforwardRingMonObj profiniteToProEt J K
    ((F.sheafPushforwardContinuous RingCat.{u + 1} K L).obj R)
  change @IsMonHom _ _ _ _ _ _
    ((profiniteToProEt.sheafPushforwardContinuous AddCommGrpCat.{u + 1} J K).monObjObj
      (((F.sheafPushforwardContinuous AddCommGrpCat.{u + 1} K L).obj
        ((sheafCompose L (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj R)))) _
  erw [← h₁, ← h₂]
  exact Sheaf.isMonHom_sheafCompose_map J (comparisonAdjointRing X E)

private lemma comparison_isMonHom (X : Scheme.{u}) (E : Type u) [NormedField E] :
    IsMonHom (comparison X E) := by
  have := comparisonAdjoint_isMonHom X E
  let a := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))
  let f : Mon.mk (Profinite.continuousCoefficientRingObj E) ⟶
      ((lowerStar AddCommGrpCat.{u + 1} (toSpecZ X)) ⋙ pointLowerStar).mapMon.obj
        (Mon.mk ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
          (continuousCoefficientRingSheaf X E))) := Mon.ofHom (comparisonAdjoint X E)
  let g := (a.mapMon.homEquiv _ _).symm f
  change IsMonHom g.hom
  exact g.isMonHom_hom

private lemma isIso_of_affine_weaklyContractible (X : Scheme.{u})
    {F G : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}} (f : F ⟶ G)
    (h : ∀ (U : X.ProEt), IsAffine U.left → PointLanWeaklyContractible X U →
      IsIso (f.hom.app (Opposite.op U))) : IsIso f := by
  apply (Sheaf.isLocallyBijective_iff_isIso f).mp
  constructor
  · refine ⟨fun {U} x y he ↦ ?_⟩
    obtain ⟨I, V, g, hc, ha, hw⟩ :=
      Scheme.ProEt.exists_affine_weaklyContractible_covering_family X U.unop
    apply (Scheme.ProEt.topology X).superset_covering
      ((Sieve.generate_le_iff _ _).mpr ?_) (Precoverage.generate_mem_toGrothendieck hc)
    intro W k hk
    cases hk with
    | mk i =>
      have := h (V i) (ha i) (hw i)
      apply (ConcreteCategory.bijective_of_isIso (f.hom.app _)).injective
      exact (NatTrans.naturality_apply f.hom (g i).op x).trans
        ((congrArg (G.obj.map (g i).op) he).trans
          (NatTrans.naturality_apply f.hom (g i).op y).symm)
  · refine ⟨fun {U} y ↦ ?_⟩
    obtain ⟨I, V, g, hc, ha, hw⟩ :=
      Scheme.ProEt.exists_affine_weaklyContractible_covering_family X U
    apply (Scheme.ProEt.topology X).superset_covering
      ((Sieve.generate_le_iff _ _).mpr ?_) (Precoverage.generate_mem_toGrothendieck hc)
    intro W k hk
    cases hk with
    | mk i =>
      have := h (V i) (ha i) (hw i)
      exact (ConcreteCategory.bijective_of_isIso (f.hom.app _)).surjective
        (G.obj.map (g i).op y)
private lemma pointComponentsEquiv_target (X : Scheme.{u}) (U : X.ProEt)
    [IsAffine U.left] (S T : Profinite.{u}) (b : S ⟶ T)
    (f : U ⟶ (profiniteToProEtOf X).obj S) :
    pointComponentsEquiv X U T (f ≫ (profiniteToProEtOf X).map b) =
      b.hom.hom.comp (pointComponentsEquiv X U S f) := by
  ext x
  obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe x
  change pointComponentsEquiv X U T (f ≫ (profiniteToProEtOf X).map b)
      (ConnectedComponents.mk x) = b (pointComponentsEquiv X U S f (ConnectedComponents.mk x))
  rw [pointComponentsEquiv_apply, pointComponentsEquiv_apply]
  change ((LocallyConstant.homeomorphPrimeSpectrum (T := T) (R := ℤ)).symm
      (relativeMapEquiv X U T (f ≫ (profiniteToProEtOf X).map b) x)).1 = _
  rw [relativeMapEquiv_target]
  exact profiniteProjection_natural S T b _

private noncomputable def canonicalComponentArrow (X : Scheme.{u}) (U : X.ProEt)
    [IsAffine U.left] :
    U ⟶ (profiniteToProEtOf X).obj (Profinite.of (ConnectedComponents U.left)) :=
  (pointComponentsEquiv X U _).symm (ContinuousMap.id _)

private noncomputable def canonicalComponentArrow_terminal (X : Scheme.{u}) (U : X.ProEt)
    [IsAffine U.left] :
    IsTerminal (CostructuredArrow.mk (S := (profiniteToProEtOf X).op)
      (canonicalComponentArrow X U).op) := by
  let T := Profinite.of (ConnectedComponents U.left)
  refine IsTerminal.ofUniqueHom
    (fun A ↦ CostructuredArrow.homMk
      (ConcreteCategory.ofHom (pointComponentsEquiv X U A.left.unop A.hom.unop)).op ?_) ?_
  · apply Quiver.Hom.unop_inj
    change canonicalComponentArrow X U ≫ (profiniteToProEtOf X).map _ = A.hom.unop
    apply (pointComponentsEquiv X U A.left.unop).injective
    rw [pointComponentsEquiv_target]
    simp only [canonicalComponentArrow, Equiv.apply_symm_apply]
    rfl
  · intro A f
    apply CostructuredArrow.hom_ext
    apply Quiver.Hom.unop_inj
    have h := congrArg Quiver.Hom.unop (CostructuredArrow.w f)
    change canonicalComponentArrow X U ≫ (profiniteToProEtOf X).map f.left.unop =
      A.hom.unop at h
    have h' := congrArg (pointComponentsEquiv X U A.left.unop) h
    rw [pointComponentsEquiv_target] at h'
    simp only [canonicalComponentArrow, Equiv.apply_symm_apply] at h'
    exact ConcreteCategory.hom_ext _ _ (congrFun (congrArg DFunLike.coe h') ·)

private noncomputable def kanComparison (X : Scheme.{u}) (E : Type u) [NormedField E] :
    (profiniteToProEtOf X).op.lan.obj (Profinite.continuousCoefficientRingObj E).obj ⟶
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
          (continuousCoefficientRingSheaf X E)).obj :=
  (((profiniteToProEtOf X).op.lanAdjunction AddCommGrpCat.{u + 1}).homEquiv _ _).symm
    (comparisonAdjoint X E).hom

private lemma kanComparison_unit (X : Scheme.{u}) (E : Type u) [NormedField E] :
    (profiniteToProEtOf X).op.lanUnit.app (Profinite.continuousCoefficientRingObj E).obj ≫
      Functor.whiskerLeft (profiniteToProEtOf X).op (kanComparison X E) =
        (comparisonAdjoint X E).hom := by
  have h := (((profiniteToProEtOf X).op.lanAdjunction AddCommGrpCat.{u + 1}).homEquiv
    (Profinite.continuousCoefficientRingObj E).obj
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
        (continuousCoefficientRingSheaf X E)).obj).apply_symm_apply (comparisonAdjoint X E).hom
  dsimp only [kanComparison]
  rw [← Functor.lanAdjunction_unit]
  exact h

private lemma kanComparison_isIso (X : Scheme.{u}) (E : Type u) [NormedField E]
    [TotallyDisconnectedSpace E] (U : X.ProEt) [IsAffine U.left]
    (P : X.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    (η : (Profinite.continuousCoefficientRingObj E).obj ⟶ (profiniteToProEtOf X).op ⋙ P)
    (σ : P ⟶ ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
        (continuousCoefficientRingSheaf X E)).obj)
    (hp : (Functor.LeftExtension.mk P η).IsPointwiseLeftKanExtension)
    (hσ : η ≫ Functor.whiskerLeft (profiniteToProEtOf X).op σ =
      (comparisonAdjoint X E).hom) : IsIso (σ.app (Opposite.op U)) := by
  let T := Profinite.of (ConnectedComponents U.left)
  let q := canonicalComponentArrow X U
  let a := η.app (Opposite.op T) ≫ P.map q.op
  have hi' := (hp (Opposite.op U)).isIso_ι_app_of_isTerminal
    (CostructuredArrow.mk (S := (profiniteToProEtOf X).op) q.op)
    (canonicalComponentArrow_terminal X U)
  have hi : IsIso a := hi'
  let Q := ((sheafCompose (Scheme.ProEt.topology X)
    (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
      (continuousCoefficientRingSheaf X E)).obj
  have h : a ≫ σ.app (Opposite.op U) =
      (comparisonAdjoint X E).hom.app (Opposite.op T) ≫ Q.map q.op := by
    dsimp only [a]
    rw [Category.assoc, σ.naturality]
    exact congrArg (fun f ↦ f ≫ Q.map q.op)
      (congr_app hσ (Opposite.op T))
  have hq (x : U.left) : profiniteTestProjection X T (q.left x) = ConnectedComponents.mk x := by
    have h := congrFun (congrArg DFunLike.coe
      ((pointComponentsEquiv X U T).apply_symm_apply (ContinuousMap.id _)))
      (ConnectedComponents.mk x)
    rw [pointComponentsEquiv_apply] at h
    exact h
  have hbij : Function.Bijective
      ((comparisonAdjoint X E).hom.app (Opposite.op T) ≫ Q.map q.op) := by
    constructor
    · intro f g he
      apply ULift.ext
      ext t
      obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe t
      have h := congrArg (fun f ↦ f.down x) he
      change f.down (profiniteTestProjection X T (q.left x)) =
        g.down (profiniteTestProjection X T (q.left x)) at h
      simpa only [hq] using h
    · intro f
      refine ⟨ULift.up ⟨f.down.continuous.connectedComponentsLift,
        f.down.continuous.connectedComponentsLift_continuous⟩, ?_⟩
      apply ULift.ext
      ext x
      change f.down.continuous.connectedComponentsLift
        (profiniteTestProjection X T (q.left x)) = f.down x
      rw [hq, Continuous.connectedComponentsLift_apply_coe]
  have : IsIso (a ≫ σ.app (Opposite.op U)) := by
    rw [h]
    exact (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  exact IsIso.of_isIso_comp_left a _

private lemma comparison_basis_isIso (X : Scheme.{u}) (E : Type u) [NormedField E]
    [TotallyDisconnectedSpace E] (U : X.ProEt) [IsAffine U.left]
    (wU : PointLanWeaklyContractible X U) :
    IsIso ((comparison X E).hom.app (Opposite.op U)) := by
  let F := profiniteToProEtOf X
  let J := coherentTopology Profinite.{u}
  let K := Scheme.ProEt.topology X
  let Λ := Profinite.continuousCoefficientRingObj E
  let H := (sheafCompose K (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
    (continuousCoefficientRingSheaf X E)
  have : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)).IsContinuous
      (Scheme.ProEt.topology specZ) (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isContinuous_overPullback (toSpecZ X)
  have : F.IsContinuous J K := by
    exact Functor.isContinuous_comp profiniteToProEt
      (MorphismProperty.Over.pullback @WeaklyEtale ⊤ (toSpecZ X)) J
      (Scheme.ProEt.topology specZ) K
  let a := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))
  let b := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous F
    AddCommGrpCat.{u + 1} J K
  let e := Adjunction.leftAdjointUniq a b
  let f := (b.homEquiv Λ H).symm (comparisonAdjoint X E)
  have hcomp : comparison X E = e.hom.app Λ ≫ f := by
    apply (a.homEquiv Λ H).injective
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [comparison, Equiv.apply_symm_apply]
    change comparisonAdjoint X E = (b.homEquiv Λ H) f
    exact ((b.homEquiv Λ H).apply_symm_apply (comparisonAdjoint X E)).symm
  let P := F.op.lan.obj Λ.obj
  let η := F.op.lanUnit.app Λ.obj
  let hp := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension P η
  have hu := (proEtale_sheafification_wcontractible_sections X).2.1 Λ P η hp U
    inferInstance wU
  have : IsIso ((toSheafify K P).app (Opposite.op U)) := hu.1
  have hunit : (toSheafify K P).app (Opposite.op U) ≫ f.hom.app (Opposite.op U) =
      (kanComparison X E).app (Opposite.op U) := by
    change (((sheafificationAdjunction K AddCommGrpCat.{u + 1}).homEquiv P H)
      f).app (Opposite.op U) = _
    simp only [ObjectProperty.ι_obj,
      Functor.sheafPullbackConstruction.sheafAdjunctionContinuous,
      Adjunction.restrictFullyFaithful, Functor.id_obj, Functor.comp_obj,
      Functor.whiskeringLeft_obj_obj, Functor.FullyFaithful.homEquiv,
      Functor.FullyFaithful.id, Iso.refl_symm, Equiv.trans_def, Adjunction.comp_homEquiv,
      Equiv.symm_mk, Adjunction.mkOfHomEquiv_homEquiv, Equiv.symm_trans,
      Iso.homCongr_symm, Equiv.trans_apply, Equiv.coe_fn_mk, ObjectProperty.ι_map,
      Iso.homCongr_apply, Iso.refl_inv, Iso.symm_hom, Iso.app_inv, NatTrans.id_app,
      Category.id_comp, Iso.symm_inv, Iso.app_hom, Iso.refl_hom, Category.comp_id,
      kanComparison, f, b]
    erw [Category.id_comp, Category.comp_id, Equiv.apply_symm_apply]
  have : IsIso ((kanComparison X E).app (Opposite.op U)) :=
    kanComparison_isIso X E U P η (kanComparison X E) hp (kanComparison_unit X E)
  have : IsIso (f.hom.app (Opposite.op U)) := by
    have : IsIso ((toSheafify K P).app (Opposite.op U) ≫ f.hom.app (Opposite.op U)) := by
      rw [hunit]
      infer_instance
    exact IsIso.of_isIso_comp_left ((toSheafify K P).app (Opposite.op U)) _
  rw [hcomp]
  change IsIso ((e.hom.app Λ).hom.app (Opposite.op U) ≫ f.hom.app (Opposite.op U))
  infer_instance

/-- The condensed coefficient ring is the ring sheaf of continuous functions on site objects.
Source: Hemo--Richarz--Scholbach, Example 3.1
(blueprint: lem-weil-pbc-condensed-lfp-local-triviality).
Proof: define the adjoint by composing each test function with |X[S]| → S; naturality
of the projection gives a morphism of ring sheaves. For an affine U, the universal map
U → X[π₀(U)] is terminal in the opposite comma category, so its Kan cocone leg is
invertible. The resulting comparison is composition with U → π₀(U), a bijection on
continuous E-valued functions because the finite normed extension E is totally disconnected.
Sheafification does not change these sections on weakly contractible affines. Uniqueness
of left adjoints identifies this sheafified Kan construction with the given composite
inverse image. Weakly contractible affine covers detect isomorphisms, proving the ring-sheaf
comparison invertible. The displayed adjoint equations determine its uniqueness. -/
theorem existsUnique_condensedFieldContinuousMapIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X] :
    ∃! e : Mon.mk (condensedRingObj (Profinite.continuousCoefficientRingObj E) X) ≅
        Mon.mk ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ RingCat.{u + 1} AddCommGrpCat.{u + 1})).obj
            (continuousCoefficientRingSheaf X E)),
      ∀ (S : Profinite.{u}) (f : C(S, E)),
        (((pointUpperStarLowerStarAdjunction.comp
            (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))).homEquiv
              _ _ e.hom.hom).hom.app (Opposite.op S)) (ULift.up f) =
          ULift.up (f.comp (profiniteTestProjection X S)) := by
  let e₀ := (Module.finBasis ℚ_[l] E).equivFunL.toHomeomorph
  have : TotallyDisconnectedSpace E :=
    e₀.isEmbedding.isTotallyDisconnected_range.mp
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)
  have := comparison_isMonHom X E
  have := isIso_of_affine_weaklyContractible X (comparison X E) (fun U hU wU ↦ by
    let _ := hU
    exact comparison_basis_isIso X E U wU)
  let e := Mon.mkIso' (asIso (comparison X E))
  refine ⟨e, fun S f ↦ comparison_eq X E S f, ?_⟩
  intro e' he'
  apply Iso.ext
  apply Mon.Hom.ext
  apply ((pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (toSpecZ X))).homEquiv _ _).injective
  ext1
  apply NatTrans.ext
  funext S
  apply ConcreteCategory.hom_ext
  intro f
  cases f with
  | up f => exact (he' S.unop f).trans (comparison_eq X E S.unop f).symm

/-- Local finite presentations over continuous field coefficients are locally finite free.
Source: Hemo--Richarz--Scholbach, Example 3.1, with the agent rank/descent argument
(blueprint: lem-weil-pbc-condensed-lfp-local-triviality).
Proof: use the preceding continuous-function realization. Pull a finite presentation to a
geometric point; inverse image and evaluation preserve cokernels, and covers of a geometric
point split. Its dimension is independent of the algebraically closed representative.
The presentation matrix consists of continuous functions, so the dimension is n minus its
pointwise rank. Flat going-down lifts generalizations through presentation covers.
Continuous functions to the Hausdorff field E agree at comparable points, hence the rank
descends and is constant on specializations. Noetherianity gives finitely many irreducible
components and sobriety gives their generic points. Rank levels are therefore clopen.
Restrict presentations to these levels. Nonvanishing loci of maximal-rank minors cover;
Gaussian elimination using the continuous inverse of each invertible minor reduces the
matrix to an identity block and a Schur complement. The latter vanishes pointwise, hence
is zero as a matrix of functions. Its cokernel is finite free. For rank zero use the zero
matrix directly. Composing the covers proves the assertion, including the empty scheme.
All cokernels are ordinary sheaf cokernels; no completeness hypothesis is used. -/
theorem exists_finiteFree_cover_of_condensedField_lfp
    (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X))
    (hP : IsLocallyFinitelyPresented
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X) P) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : C.I₀,
      Mod.IsFree
        ((upperStar AddCommGrpCat.{u + 1} (C.f i)).obj
          (condensedRingObj (Profinite.continuousCoefficientRingObj E) X))
        (((upperStar AddCommGrpCat.{u + 1} (C.f i)).mapMod
          (condensedRingObj (Profinite.continuousCoefficientRingObj E) X)).obj P) := sorry

private lemma fp_map {X Y : Scheme.{u}}
    (R : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
    (T : Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}) [MonObj R] [MonObj T]
    (F : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R ⥤
      Mod (Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}) T)
    [F.Additive] [Limits.PreservesFiniteColimits F]
    (e : F.obj (Mod.regular R) ≅ Mod.regular T)
    {M : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) R}
    (h : Mod.IsFinitelyPresented R M) : Mod.IsFinitelyPresented T (F.obj M) := by
  open Limits in
  rcases h with ⟨n, m, f, ⟨i⟩⟩
  let en (n : ℕ) : F.obj (Mod.finiteFree R n) ≅ Mod.finiteFree T n :=
    F.mapBiproduct (fun _ : Fin n ↦ Mod.regular R) ≪≫
      Limits.biproduct.mapIso (fun _ ↦ e)
  let f' : Mod.finiteFree T m ⟶ Mod.finiteFree T n :=
    (en m).inv ≫ F.map f ≫ (en n).hom
  exact ⟨n, m, f', ⟨F.mapIso i ≪≫ Limits.PreservesCokernel.iso F f ≪≫
    Limits.cokernel.mapIso (F.map f) f' (en m) (en n) (by simp [f'])⟩⟩

private lemma fp_comap {X : Scheme.{u}}
    {R T : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}}
    [MonObj R] [MonObj T]
    (φ : R ⟶ T) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) T}
    (h : Mod.IsFinitelyPresented T M) :
    Mod.IsFinitelyPresented R ((Mod.comap φ).obj M) := by
  let eqv : Mod _ T ≌ Mod _ R :=
    CategoryTheory.Equivalence.mk (Mod.comap φ) (Mod.comap (inv φ))
      ((Mod.comapId T).symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapComp (inv φ) φ)
      ((Mod.comapComp φ (inv φ)).symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapId R)
  have : (Mod.comap φ).IsEquivalence := eqv.isEquivalence_functor
  exact fp_map T R (Mod.comap φ) (by
    simpa using (Mod.regularIsoOfIsIso (inv φ))) h

private lemma lfp_comap {X : Scheme.{u}}
    {R T : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}}
    [MonObj R] [MonObj T]
    (φ : R ⟶ T) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) T}
    (h : IsLocallyFinitelyPresented T M) :
    IsLocallyFinitelyPresented R ((Mod.comap φ).obj M) := by
  obtain ⟨C, hC⟩ := h
  refine ⟨C, fun i ↦ ?_⟩
  let F := upperStar AddCommGrpCat.{u + 1} (C.f i)
  obtain ⟨n, m, f, ⟨e⟩⟩ := fp_comap (F.map φ) (hC i)
  exact ⟨n, m, f, ⟨(F.mapModComapIso φ).app M ≪≫ e⟩⟩

private lemma free_comap {X : Scheme.{u}}
    {R T : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}}
    [MonObj R] [MonObj T]
    (φ : R ⟶ T) [IsMonHom φ] [IsIso φ]
    {M : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) T}
    (h : Mod.IsFree T M) : Mod.IsFree R ((Mod.comap φ).obj M) := by
  let eqv : Mod _ T ≌ Mod _ R :=
    CategoryTheory.Equivalence.mk (Mod.comap φ) (Mod.comap (inv φ))
      ((Mod.comapId T).symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapComp (inv φ) φ)
      ((Mod.comapComp φ (inv φ)).symm ≪≫ Mod.comapCongr (by simp) ≪≫ Mod.comapId R)
  have : (Mod.comap φ).IsEquivalence := eqv.isEquivalence_functor
  obtain ⟨n, ⟨e⟩⟩ := h
  refine ⟨n, ⟨(Mod.comap φ).mapIso e ≪≫ ?_⟩⟩
  exact (Mod.comap φ).mapBiproduct (fun _ : Fin n ↦ Mod.regular T) ≪≫
    Limits.biproduct.mapIso (fun _ ↦ by simpa using Mod.regularIsoOfIsIso (inv φ))

/-- The local triviality assertion applies on every noetherian locally closed stratum.
Source: the concluding application in the agent rank/descent argument accompanying
Hemo--Richarz--Scholbach, Example 3.1
(blueprint: lem-weil-pbc-condensed-lfp-local-triviality).
Proof: restrict the module to a stratum of its finite locally closed stratification.
The coefficient composition comparison identifies the restricted ring with the condensed
coefficient ring of the stratum. Apply the local triviality theorem there, to the finite
presentations in the stratified constructibility hypothesis. Pullback preserves the
coefficient comparison, so its finite free modules give exactly the displayed ones.
This includes empty strata, rank zero, and presentations with zero rows or columns. -/
theorem exists_finiteFree_cover_on_condensedField_strata
    (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (S : Scheme.LocallyClosedStratification X)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1})
      (condensedRingObj (Profinite.continuousCoefficientRingObj E) X))
    (hP : ∀ a : Fin S.n,
      IsLocallyFinitelyPresented
        ((upperStar AddCommGrpCat.{u + 1} (S.immersion a)).obj
          (condensedRingObj (Profinite.continuousCoefficientRingObj E) X))
        (((upperStar AddCommGrpCat.{u + 1} (S.immersion a)).mapMod
          (condensedRingObj (Profinite.continuousCoefficientRingObj E) X)).obj P)) :
    ∀ (a : Fin S.n), TopologicalSpace.NoetherianSpace (S.domain a) →
      ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage (S.domain a), ∀ i : C.I₀,
        Mod.IsFree
          ((upperStar AddCommGrpCat.{u + 1} (C.f i)).obj
            ((upperStar AddCommGrpCat.{u + 1} (S.immersion a)).obj
              (condensedRingObj (Profinite.continuousCoefficientRingObj E) X)))
          (((upperStar AddCommGrpCat.{u + 1} (C.f i)).mapMod
            ((upperStar AddCommGrpCat.{u + 1} (S.immersion a)).obj
              (condensedRingObj (Profinite.continuousCoefficientRingObj E) X))).obj
            (((upperStar AddCommGrpCat.{u + 1} (S.immersion a)).mapMod
              (condensedRingObj (Profinite.continuousCoefficientRingObj E) X)).obj P)) := by
  intro a ha
  let Λ := Profinite.continuousCoefficientRingObj E
  let R := (upperStar AddCommGrpCat.{u + 1} (S.immersion a)).obj (condensedRingObj Λ X)
  let M := ((upperStar AddCommGrpCat.{u + 1} (S.immersion a)).mapMod
    (condensedRingObj Λ X)).obj P
  let φ := condensedPullbackHom Λ (S.immersion a)
  let Q := (Mod.comap (inv φ)).obj M
  have hQ : IsLocallyFinitelyPresented (condensedRingObj Λ (S.domain a)) Q :=
    lfp_comap (inv φ) (hP a)
  obtain ⟨C, hC⟩ := exists_finiteFree_cover_of_condensedField_lfp l E (S.domain a) Q hQ
  refine ⟨C, fun i ↦ ?_⟩
  let F := upperStar AddCommGrpCat.{u + 1} (C.f i)
  let e : (Mod.comap φ).obj Q ≅ M :=
    ((Mod.comapComp φ (inv φ)).symm ≪≫
      Mod.comapCongr (IsIso.hom_inv_id φ) ≪≫ Mod.comapId R).app M
  obtain ⟨n, ⟨f⟩⟩ := free_comap (F.map φ) (hC i)
  exact ⟨n, ⟨(F.mapMod R).mapIso e.symm ≪≫ (F.mapModComapIso φ).app Q ≪≫ f⟩⟩

end AlgebraicGeometry.ProEtale
