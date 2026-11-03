/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.StandardPasting.StandardSectionPastingData
import WeilConjectures.AlgebraicGeometry.SectionPullbackTensorInterchange
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalPasting.PurityDiagonalOpenRestriction

/-! # The concrete pulled sigma square for standard affine pairs
(blueprint: lem-route-standard-section-pasting-base-change-sigma).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.StandardPasting
open DiagonalPasting

private theorem tensorComparison_eq_tensorIso (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent P.Coefficient (Spec (.of P.field.k))]
    {X : Scheme.{u}} {K K' M M' : Etale.DerivedCategoryModule P.Coefficient X}
    (a : K ≅ K') (b : M ≅ M') :
    tensorComparison P.Coefficient P a b = tensorIso a b := by
  apply Iso.ext
  simp only [tensorComparison_hom, tensorIso_hom, Etale.derivedTensorHom,
    Etale.derivedTensor, curriedTensor_map_app, curriedTensor_obj_map,
    MonoidalCategory.tensorHom_def]

set_option maxHeartbeats 1500000 in
-- Derived pullback compositor expressions require a larger elaboration budget.
private theorem tensor_square_transport
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
    [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    [Etale.UpperStarPreservesFlat A]
    {B B' X X' : Scheme.{u}} {v : B' ⟶ B} {s : B ⟶ X} {s' : B' ⟶ X'}
    {r : X' ⟶ X} (sq : CommSq v s' s r)
    (K M N : DerivedCategory (Sheaf X.smallEtaleTopology A))
    (K' M' N' : DerivedCategory (Sheaf X'.smallEtaleTopology A))
    (a : (Etale.upperStar A r).leftDerivedFunctor.obj K ≅ K')
    (b : (Etale.upperStar A r).leftDerivedFunctor.obj M ≅ M')
    (c : (Etale.upperStar A r).leftDerivedFunctor.obj N ≅ N')
    (n : K ⊗ M ≅ N) (n' : K' ⊗ M' ≅ N')
    (h : (Etale.upperStar A r).leftDerivedFunctor.mapIso n ≪≫ c =
      Etale.leftDerivedUpperStarTensorIso A r K M ≪≫ tensorIso a b ≪≫ n') :
    let F := (Etale.upperStar A v).leftDerivedFunctor
    let S := (Etale.upperStar A s).leftDerivedFunctor
    let S' := (Etale.upperStar A s').leftDerivedFunctor
    let H := (Etale.derivedSquareUpperStarIso A sq).symm
    F.mapIso ((Etale.leftDerivedUpperStarTensorIso A s K M).symm ≪≫ S.mapIso n) ≪≫
        H.app N ≪≫ S'.mapIso c =
      Etale.leftDerivedUpperStarTensorIso A v (S.obj K) (S.obj M) ≪≫
        tensorIso (H.app K ≪≫ S'.mapIso a) (H.app M ≪≫ S'.mapIso b) ≪≫
        (Etale.leftDerivedUpperStarTensorIso A s' K' M').symm ≪≫ S'.mapIso n' := by
  dsimp only
  let F := (Etale.upperStar A v).leftDerivedFunctor
  let S := (Etale.upperStar A s).leftDerivedFunctor
  let S' := (Etale.upperStar A s').leftDerivedFunctor
  let R := (Etale.upperStar A r).leftDerivedFunctor
  let H := (Etale.derivedSquareUpperStarIso A sq).symm
  have hn : F.mapIso (S.mapIso n) ≪≫ H.app N =
      H.app (K ⊗ M) ≪≫ S'.mapIso (R.mapIso n) := by
    apply Iso.ext
    exact H.hom.naturality n.hom
  have ht := Etale.sectionPullbackTensorInterchange A sq K M
  have hnat :
      (Etale.leftDerivedUpperStarTensorIso A s' (R.obj K) (R.obj M)).symm ≪≫
        S'.mapIso (tensorIso a b) =
      tensorIso (S'.mapIso a) (S'.mapIso b) ≪≫
        (Etale.leftDerivedUpperStarTensorIso A s' K' M').symm := by
    apply Iso.ext
    dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, tensorIso_hom]
    apply (Iso.inv_comp_eq
      (Etale.leftDerivedUpperStarTensorIso A s' (R.obj K) (R.obj M))).2
    rw [← Category.assoc]
    apply (Iso.eq_comp_inv (Etale.leftDerivedUpperStarTensorIso A s' K' M')).2
    exact (Etale.leftDerivedUpperStarTensorComparison_naturality A s' a.hom b.hom).symm
  have hcomp :
      tensorIso (H.app K) (H.app M) ≪≫ tensorIso (S'.mapIso a) (S'.mapIso b) =
      tensorIso (H.app K ≪≫ S'.mapIso a) (H.app M ≪≫ S'.mapIso b) := by
    apply Iso.ext
    simp only [Iso.trans_hom, tensorIso_hom, tensorHom_comp_tensorHom]
  dsimp only [F, S, S', R, H] at hn ht hnat hcomp
  simp only [Functor.mapIso_trans, Iso.trans_assoc]
  rw [← Iso.trans_assoc (F.mapIso (S.mapIso n)), hn]
  simp only [Iso.trans_assoc]
  rw [← Functor.mapIso_trans, h]
  simp only [Functor.mapIso_trans]
  rw [← Iso.trans_assoc
    (F.mapIso (Etale.leftDerivedUpperStarTensorIso A s K M).symm), ht]
  simp only [Iso.trans_assoc, Functor.mapIso_symm, Iso.symm_self_id_assoc]
  rw [← Iso.trans_assoc
    (Etale.leftDerivedUpperStarTensorIso A s' (R.obj K) (R.obj M)).symm, hnat]
  simp only [Iso.trans_assoc]
  rw [← Iso.trans_assoc (tensorIso (H.app K) (H.app M)), hcomp]

set_option maxHeartbeats 1500000 in
-- Derived pullback compositor expressions require a larger elaboration budget.
private theorem beta_congr
    (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent P.Coefficient (Spec (.of P.field.k))]
    {X X' Y Y' : Scheme.{u}} {f g : X ⟶ Y} {f' g' : X' ⟶ Y'}
    {a : X' ⟶ X} {b : Y' ⟶ Y}
    [HasCompactification f] [HasCompactification g]
    [HasCompactification f'] [HasCompactification g'] [QuasiCompact f'] [QuasiCompact g']
    (hf : f = g) (hf' : f' = g') (sq : IsPullback a f' f b)
    (sq' : IsPullback a g' g b) :
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) a).leftDerivedFunctor.map
        (dualizingCongr P.Coefficient P hf).hom ≫
      Etale.dualizingComplexBaseChangeMap P.Coefficient sq' =
    Etale.dualizingComplexBaseChangeMap P.Coefficient sq ≫
      (dualizingCongr P.Coefficient P hf').hom := by
  subst g
  subst g'
  simp only [dualizingCongr, Iso.refl_hom, Category.comp_id]
  rw [(Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) a).leftDerivedFunctor.map_id,
    Category.id_comp]

set_option maxHeartbeats 1500000 in
-- Derived pullback compositor expressions require a larger elaboration budget.
/-- Sigma base change for the actual ordered affine tower, before zero pullback.
Source: composition coherence Step 1, Step 4 of standard section-pasting base change
(blueprint: lem-route-standard-section-pasting-base-change-affine-sigma).
Proof: specialize the sigma base-change mate equation to the two block projections.
The affine-space Cartesian squares are the required squares. Their vertical paste is
identified with the total affine projection square using q p_e = p_(d+e).
Equality transport of the dualizing complex commutes with beta, by substitution;
this puts both total endpoints into the stated canonical coordinates.
-/
theorem affine_sigma_base_change (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent P.Coefficient (Spec (.of P.field.k))]
    {B B' : Scheme.{u}} [IsAffine B] [IsAffine B']
    [IsNoetherian B] [IsNoetherian B']
    (d e : ℕ) (b : B' ⟶ B) [Etale b]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    [LocallyOfFiniteType b] [QuasiCompact b] :
    letI := (affineGeometry d e B).2.2.2.2.1
    letI := (affineGeometry d e B).2.2.2.2.2.1
    letI := (affineGeometry d e B).2.2.2.2.2.2.1
    letI := (affineGeometry d e B).2.2.2.2.2.2.2.1
    letI := (affineGeometry d e B').2.2.2.2.1
    letI := (affineGeometry d e B').2.2.2.2.2.1
    letI := (affineGeometry d e B').2.2.2.2.2.2.1
    letI := (affineGeometry d e B').2.2.2.2.2.2.2.1
    letI := affineDimension e B
    letI := affineDimension e B'
    letI := affineDimension (d+e) B
    letI := affineDimension (d+e) B'
    let H := (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.map (ULift.{u} (Fin (d+e))) b)).leftDerivedFunctor
    let ae := beta P.Coefficient P e (AffineSpace.isPullback_map b) (pr e B ≫ aB)
    let a := beta P.Coefficient P d (geometry d e b).2.2 (pr (d+e) B ≫ aB)
    let a₂ := Etale.sectionCoherencePullbackIso P.Coefficient
      (AffineSpace.map (ULift.{u} (Fin (d+e))) b) (q d e B) (q d e B')
      (AffineSpace.map (ULift.{u} (Fin e)) b) (geometry d e b).1 _ ≪≫
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) (q d e B')).leftDerivedFunctor.mapIso ae
    H.mapIso (sigma P.Coefficient P d (q d e B) (pr e B) (pr (d+e) B ≫ aB) ≪≫
        dualizingCongr P.Coefficient P (affineGeometry d e B).2.2.2.1) ≪≫
      beta P.Coefficient P (d+e) (AffineSpace.isPullback_map b) (pr (d+e) B ≫ aB) =
    Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient)
      (AffineSpace.map (ULift.{u} (Fin (d+e))) b) _ _ ≪≫
      tensorComparison P.Coefficient P a a₂ ≪≫
      sigma P.Coefficient P d (q d e B') (pr e B') (pr (d+e) B' ≫ b ≫ aB) ≪≫
        dualizingCongr P.Coefficient P (affineGeometry d e B').2.2.2.1 := by
  let := (affineGeometry d e B).2.2.2.2.1
  let := (affineGeometry d e B).2.2.2.2.2.1
  let := (affineGeometry d e B).2.2.2.2.2.2.1
  let := (affineGeometry d e B).2.2.2.2.2.2.2.1
  let := (affineGeometry d e B').2.2.2.2.1
  let := (affineGeometry d e B').2.2.2.2.2.1
  let := (affineGeometry d e B').2.2.2.2.2.2.1
  let := (affineGeometry d e B').2.2.2.2.2.2.2.1
  let := affineDimension e B
  let := affineDimension e B'
  let := affineDimension (d+e) B
  let := affineDimension (d+e) B'
  let : B.Over (Spec (.of P.field.k)) := ⟨aB⟩
  let : B'.Over (Spec (.of P.field.k)) := ⟨b ≫ aB⟩
  let : (A e B).Over (Spec (.of P.field.k)) := ⟨pr e B ≫ aB⟩
  let : (A e B').Over (Spec (.of P.field.k)) := ⟨pr e B' ≫ b ≫ aB⟩
  let : (A (d+e) B).Over (Spec (.of P.field.k)) := ⟨pr (d+e) B ≫ aB⟩
  let : (A (d+e) B').Over (Spec (.of P.field.k)) := ⟨pr (d+e) B' ≫ b ≫ aB⟩
  have : LocallyOfFiniteType (B ↘ Spec (.of P.field.k)) := inferInstanceAs
    (LocallyOfFiniteType aB)
  have : QuasiCompact (B ↘ Spec (.of P.field.k)) := inferInstanceAs (QuasiCompact aB)
  have : LocallyOfFiniteType (B' ↘ Spec (.of P.field.k)) := inferInstanceAs
    (LocallyOfFiniteType (b ≫ aB))
  have : QuasiCompact (B' ↘ Spec (.of P.field.k)) := inferInstanceAs
    (QuasiCompact (b ≫ aB))
  have : LocallyOfFiniteType ((A e B) ↘ Spec (.of P.field.k)) := inferInstanceAs
    (LocallyOfFiniteType (pr e B ≫ aB))
  have : QuasiCompact ((A e B) ↘ Spec (.of P.field.k)) := inferInstanceAs
    (QuasiCompact (pr e B ≫ aB))
  have : LocallyOfFiniteType ((A e B') ↘ Spec (.of P.field.k)) := inferInstanceAs
    (LocallyOfFiniteType (pr e B' ≫ b ≫ aB))
  have : QuasiCompact ((A e B') ↘ Spec (.of P.field.k)) := inferInstanceAs
    (QuasiCompact (pr e B' ≫ b ≫ aB))
  have : LocallyOfFiniteType ((A (d+e) B) ↘ Spec (.of P.field.k)) := inferInstanceAs
    (LocallyOfFiniteType (pr (d+e) B ≫ aB))
  have : QuasiCompact ((A (d+e) B) ↘ Spec (.of P.field.k)) := inferInstanceAs
    (QuasiCompact (pr (d+e) B ≫ aB))
  have : LocallyOfFiniteType ((A (d+e) B') ↘ Spec (.of P.field.k)) := inferInstanceAs
    (LocallyOfFiniteType (pr (d+e) B' ≫ b ≫ aB))
  have : QuasiCompact ((A (d+e) B') ↘ Spec (.of P.field.k)) := inferInstanceAs
    (QuasiCompact (pr (d+e) B' ≫ b ≫ aB))
  have : (q d e B).IsOver (Spec (.of P.field.k)) :=
    ⟨by
      change q d e B ≫ (pr e B ≫ aB) = pr (d+e) B ≫ aB
      rw [← Category.assoc, (affineGeometry d e B).2.2.2.1]⟩
  have : (q d e B').IsOver (Spec (.of P.field.k)) :=
    ⟨by
      change q d e B' ≫ (pr e B' ≫ b ≫ aB) = pr (d+e) B' ≫ b ≫ aB
      rw [← Category.assoc, (affineGeometry d e B').2.2.2.1]⟩
  have : (pr e B).IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  have : (pr e B').IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  have : b.IsOver (Spec (.of P.field.k)) := ⟨rfl⟩
  have : (AffineSpace.map (ULift.{u} (Fin e)) b).IsOver (Spec (.of P.field.k)) :=
    ⟨by
      change AffineSpace.map (ULift.{u} (Fin e)) b ≫ (pr e B ≫ aB) =
        pr e B' ≫ b ≫ aB
      rw [← Category.assoc, AffineSpace.map_over, Category.assoc]⟩
  have : (AffineSpace.map (ULift.{u} (Fin (d+e))) b).IsOver
      (Spec (.of P.field.k)) :=
    ⟨by
      change AffineSpace.map (ULift.{u} (Fin (d+e))) b ≫ (pr (d+e) B ≫ aB) =
        pr (d+e) B' ≫ b ≫ aB
      rw [← Category.assoc, AffineSpace.map_over, Category.assoc]⟩
  have : LocallyOfFiniteType (AffineSpace.map (ULift.{u} (Fin e)) b) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (AffineSpace.isPullback_map b).flip inferInstance
  have : QuasiCompact (AffineSpace.map (ULift.{u} (Fin e)) b) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (AffineSpace.isPullback_map b).flip inferInstance
  have : LocallyOfFiniteType (AffineSpace.map (ULift.{u} (Fin (d+e))) b) :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
      (AffineSpace.isPullback_map b).flip inferInstance
  have : QuasiCompact (AffineSpace.map (ULift.{u} (Fin (d+e))) b) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact)
      (AffineSpace.isPullback_map b).flip inferInstance
  obtain ⟨_, _, _, _, hs, _, _, _, _⟩ :=
    ProEtale.DualizingLocality.dualizing_sigma_cocycle_locality P
  have h := hs (q d e B) d (pr e B) e (q d e B') d (pr e B') e
    (AffineSpace.map (ULift.{u} (Fin (d+e))) b)
    (AffineSpace.map (ULift.{u} (Fin e)) b) b
    (geometry d e b).2.2 (AffineSpace.isPullback_map b)
  have hc := beta_congr P (affineGeometry d e B).2.2.2.1
    (affineGeometry d e B').2.2.2.1
    ((geometry d e b).2.2.paste_vert (AffineSpace.isPullback_map b))
    (AffineSpace.isPullback_map b)
  dsimp only
  apply Iso.ext
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    beta, asIso_hom, Category.assoc]
  rw [hc]
  rw [pullSquare_eq P (AffineSpace.map (ULift.{u} (Fin (d+e))) b)
    (q d e B) (q d e B') (AffineSpace.map (ULift.{u} (Fin e)) b)
    (geometry d e b).1] at h
  simpa only [tensorComparison_hom, sigma_hom_eq, beta, asIso_hom,
    ProEtale.FiniteEtaleNormalization.beta, ProEtale.FiniteEtaleNormalization.baseChange,
    Etale.dualizingComplexBaseChangeMap,
    Iso.trans_hom, Functor.mapIso_hom, Category.assoc] using
    congrArg (fun z ↦ z ≫
      (dualizingCongr P.Coefficient P (affineGeometry d e B').2.2.2.1).hom) h

-- Keep large derived constructions atomic while identifying the concrete factors.
attribute [local irreducible] Etale.upperStar Functor.leftDerivedFunctor
  Etale.dualizingComplex sigma beta dualizingCongr

set_option maxHeartbeats 1500000 in
-- Derived pullback compositor expressions require a larger elaboration budget.
/-- The actual sigma tail, pulled along the total zero section, commutes with base change.
Source: composition coherence Step 1, Steps 4 and 6 of the standard-pair base-change
calculation (blueprint: lem-route-standard-section-pasting-base-change-sigma).
Proof: apply the sigma base-change clause of dualizing_sigma_cocycle_locality to
q : A^(d+e)_B -> A^e_B and p_e, their base changes, and the affine-space maps.
Its beta maps are the counit mates of compact-support exchange, and its sigma is
the specified tensor mate followed by the inverse exceptional compositor. Pull
this equality along z'_(d+e). The equality h_(d+e) z'_(d+e) = z_(d+e) b and
pullback-compositor naturality identify the final beta with baseChange at d+e.
The tensor-compositor law identifies the two orders of tensor pullback; naturality
moves the two beta factors through that constraint. The resulting factors are
exactly firstChange and secondChange, with their displayed square compositors.
The equality q p_e = p_(d+e) identifies the endpoints through dualizingCongr.
The tuple description of all squares and the tensor-compositor laws also apply
to zero ranks and empty bases, so no extra hypothesis is necessary.
-/
theorem sigma_baseChange_pulled (P : PurityFiniteSetting.{u})
    [HasInvertibleExponent P.Coefficient (Spec (.of P.field.k))]
    {B B' : Scheme.{u}} [IsAffine B] [IsAffine B']
    [IsNoetherian B] [IsNoetherian B']
    (d e : ℕ) (b : B' ⟶ B) [Etale b]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    [LocallyOfFiniteType b] [QuasiCompact b] :
    letI := (affineGeometry d e B).2.2.2.2.1
    letI := (affineGeometry d e B).2.2.2.2.2.1
    letI := (affineGeometry d e B).2.2.2.2.2.2.1
    letI := (affineGeometry d e B).2.2.2.2.2.2.2.1
    letI := (affineGeometry d e B').2.2.2.2.1
    letI := (affineGeometry d e B').2.2.2.2.2.1
    letI := (affineGeometry d e B').2.2.2.2.2.2.1
    letI := (affineGeometry d e B').2.2.2.2.2.2.2.1
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
        (tail P d e B aB) ≪≫ baseChange P (d+e) b aB =
      Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) b
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) (zero (d+e) B)).leftDerivedFunctor.obj
          (Etale.dualizingComplex P.Coefficient (q d e B)))
        ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) (zero (d+e) B)).leftDerivedFunctor.obj
          ((Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) (q d e B)).leftDerivedFunctor.obj
            (Etale.dualizingComplex P.Coefficient (pr e B)))) ≪≫
        tensorComparison P.Coefficient P (firstChange P d e b aB) (secondChange P d e b aB) ≪≫
        tail P d e B' (b ≫ aB) := by
  let := (affineGeometry d e B).2.2.2.2.1
  let := (affineGeometry d e B).2.2.2.2.2.1
  let := (affineGeometry d e B).2.2.2.2.2.2.1
  let := (affineGeometry d e B).2.2.2.2.2.2.2.1
  let := (affineGeometry d e B').2.2.2.2.1
  let := (affineGeometry d e B').2.2.2.2.2.1
  let := (affineGeometry d e B').2.2.2.2.2.2.1
  let := (affineGeometry d e B').2.2.2.2.2.2.2.1
  let := affineDimension e B
  let := affineDimension e B'
  let := affineDimension (d+e) B
  let := affineDimension (d+e) B'
  let C := ModuleCat.{u + 1} P.Coefficient
  let K := Etale.dualizingComplex P.Coefficient (q d e B)
  let M := (Etale.upperStar C (q d e B)).leftDerivedFunctor.obj
    (Etale.dualizingComplex P.Coefficient (pr e B))
  let N := Etale.dualizingComplex P.Coefficient (pr (d+e) B)
  let K' := Etale.dualizingComplex P.Coefficient (q d e B')
  let M' := (Etale.upperStar C (q d e B')).leftDerivedFunctor.obj
    (Etale.dualizingComplex P.Coefficient (pr e B'))
  let N' := Etale.dualizingComplex P.Coefficient (pr (d+e) B')
  let a := beta P.Coefficient P d (geometry d e b).2.2 (pr (d+e) B ≫ aB)
  let ae := beta P.Coefficient P e (AffineSpace.isPullback_map b) (pr e B ≫ aB)
  let a₂ := Etale.sectionCoherencePullbackIso P.Coefficient
    (AffineSpace.map (ULift.{u} (Fin (d+e))) b) (q d e B) (q d e B')
    (AffineSpace.map (ULift.{u} (Fin e)) b) (geometry d e b).1 _ ≪≫
    (Etale.upperStar C (q d e B')).leftDerivedFunctor.mapIso ae
  let c := beta P.Coefficient P (d+e) (AffineSpace.isPullback_map b)
    (pr (d+e) B ≫ aB)
  let n := sigma P.Coefficient P d (q d e B) (pr e B) (pr (d+e) B ≫ aB) ≪≫
    dualizingCongr P.Coefficient P (affineGeometry d e B).2.2.2.1
  let n' := sigma P.Coefficient P d (q d e B') (pr e B') (pr (d+e) B' ≫ b ≫ aB) ≪≫
    dualizingCongr P.Coefficient P (affineGeometry d e B').2.2.2.1
  have ha := affine_sigma_base_change P d e b aB
  have ha' :
      (Etale.upperStar C (AffineSpace.map (ULift.{u} (Fin (d+e))) b)).leftDerivedFunctor.mapIso
          n ≪≫ c =
        Etale.leftDerivedUpperStarTensorIso C
          (AffineSpace.map (ULift.{u} (Fin (d+e))) b) K M ≪≫ tensorIso a a₂ ≪≫ n' := by
    simpa only [tensorComparison_eq_tensorIso] using ha
  have ht := tensor_square_transport C
    (show CommSq b (zero (d+e) B') (zero (d+e) B)
      (AffineSpace.map (ULift.{u} (Fin (d+e))) b) from
      ⟨(AffineSpace.zeroSection_comp_map b).symm⟩)
    K M N K' M' N' a a₂ c n n' ha'
  let Z := (Etale.upperStar C (zero (d+e) B)).leftDerivedFunctor
  let Z' := (Etale.upperStar C (zero (d+e) B')).leftDerivedFunctor
  let H := (Etale.derivedSquareUpperStarIso C
    (show CommSq b (zero (d+e) B') (zero (d+e) B)
      (AffineSpace.map (ULift.{u} (Fin (d+e))) b) from
      ⟨(AffineSpace.zeroSection_comp_map b).symm⟩)).symm
  have htail : (Etale.leftDerivedUpperStarTensorIso C (zero (d+e) B) K M).symm ≪≫
      Z.mapIso n = tail P d e B aB := by
    simp only [tail, C, K, M, Z, n]
  have hbc : H.app N ≪≫ Z'.mapIso c = baseChange P (d+e) b aB := by
    simp only [baseChange, C, N, c, H, Z', Etale.derivedSquareUpperStarIso,
      Etale.sectionCoherencePullbackIso, Iso.trans_symm, Iso.symm_symm_eq,
      NatIso.trans_app]
  have hfirst : H.app K ≪≫ Z'.mapIso a = firstChange P d e b aB := by
    simp only [firstChange, C, K, a, H, Z', Etale.derivedSquareUpperStarIso,
      Etale.sectionCoherencePullbackIso, Iso.trans_symm, Iso.symm_symm_eq,
      NatIso.trans_app]
  have hsecond : H.app M ≪≫ Z'.mapIso a₂ = secondChange P d e b aB := by
    simp only [secondChange, C, M, a₂, ae, H, Z', Etale.derivedSquareUpperStarIso,
      Etale.sectionCoherencePullbackIso, Iso.trans_symm, Iso.symm_symm_eq,
      NatIso.trans_app]
  have htail' : (Etale.leftDerivedUpperStarTensorIso C (zero (d+e) B') K' M').symm ≪≫
      Z'.mapIso n' = tail P d e B' (b ≫ aB) := by
    simp only [tail, C, K', M', Z', n']
  dsimp only at ht
  rw [htail, hbc, hfirst, hsecond, htail'] at ht
  simpa only [tensorComparison_eq_tensorIso] using ht

end WeilConjectures.PurityFiniteSetting.StandardPasting
