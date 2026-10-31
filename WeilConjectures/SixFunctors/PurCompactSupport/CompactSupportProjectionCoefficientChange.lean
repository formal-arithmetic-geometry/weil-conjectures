/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.PurCompactSupport.IntegralCompactSupportCoefficientComparison
import all WeilConjectures.Algebra.Homology.RingedTensorSquare.RingedExchangeTensorCoherence
import WeilConjectures.SixFunctors.PurCompactSupport.ScalarPullTensorCoefficientCoherence
import WeilConjectures.SixFunctors.PurCompactSupport.OpenProjectionFactorCoefficientChange

/-! # Coefficient compatibility of the ordinary compact-support projection

Source: Stacks Project, Tags 07A4, 0D6D, 0E48 and 0E8I; the actual-map reduction
step of the blueprint projection-formula proof.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  proEtaleRingDerivedAdjunction pbcDerivedScalarAdjunction
namespace WeilConjectures.PurCompactSupport
attribute [local irreducible] scalarTensor properComparison openComparison comparison
  proEtaleCanonicalTensorComparison

private theorem leftAdjointUniq_inverse
    {A B : Type*} [Category A] [Category B]
    {L L' : A ⥤ B} {U U' : B ⥤ A}
    (a : L ⊣ U) (b : L' ⊣ U') (d : U ≅ U') :
    ((a.ofNatIsoRight d).leftAdjointUniq b).inv =
      (conjugateEquiv a b).symm d.hom := by
  ext N
  simp [Adjunction.leftAdjointUniq, conjugateEquiv_symm_apply_app,
    Adjunction.ofNatIsoRight_unit]

private theorem proper_coefficient_mate
    {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (g : U ⟶ V) :
    properComparison a g =
      (mateEquiv (proEtaleRingDerivedAdjunction g (R.ring V) (R.ring U) (R.pull g))
        (proEtaleRingDerivedAdjunction g (S.ring V) (S.ring U) (S.pull g))
        (TwoSquare.mk _ _ _ _ (scalarPull a g).inv)).natTrans := by
  let ar := proEtaleRingDerivedAdjunction g (R.ring V) (R.ring U) (R.pull g)
  let bs := proEtaleRingDerivedAdjunction g (S.ring V) (S.ring U) (S.pull g)
  let az := pbcDerivedScalarAdjunction (a.map U)
  let ay := pbcDerivedScalarAdjunction (a.map V)
  let d := proEtaleRingRestrictionDerivedDirectImage g
    (R.ring V) (S.ring V) (R.ring U) (S.ring U)
    (a.map V) (a.map U) (R.pull g) (S.pull g) (a.square g)
  let t := TwoSquare.mk _ _ _ _ (scalarPull a g).inv
  have ht : mateEquiv az ay (mateEquiv ar bs t) = TwoSquare.mk _ _ _ _ d.inv := by
    apply (TwoSquare.equivNatTrans _ _ _ _).injective
    change (mateEquiv az ay (mateEquiv ar bs t)).natTrans = d.inv
    rw [iterated_mateEquiv_conjugateEquiv]
    change conjugateEquiv (ar.comp az) (ay.comp bs)
      (((ar.comp az).ofNatIsoRight d.symm).leftAdjointUniq (ay.comp bs)).inv = d.inv
    rw [leftAdjointUniq_inverse]
    exact (conjugateEquiv (ar.comp az) (ay.comp bs)).apply_symm_apply d.inv
  have h := congrArg (fun z ↦ ((mateEquiv az ay).symm z).natTrans) ht
  simpa only [Equiv.symm_apply_apply, ar, bs, az, ay, d, t, properComparison] using h.symm

attribute [local irreducible] scalarPull projectionOpenFactor

private theorem proper_projection_coefficient_square
    {R S : Coefficients.{u}} (a : Change R S)
    {U V : Scheme.{u}} (g : U ⟶ V)
    (aU : ProEtaleTensorModel U (R.ring U))
    (aV : ProEtaleTensorModel V (R.ring V))
    (bU : ProEtaleTensorModel U (S.ring U))
    (bV : ProEtaleTensorModel V (S.ring V))
    (M : DerivedCategory (pbcModules U (R.ring U)))
    (L : DerivedCategory (pbcModules V (R.ring V))) :
    (pbcDerivedExtend (a.map V)).map
        ((proEtaleRingDerivedAdjunction g (R.ring V) (R.ring U) (R.pull g)).homEquiv _ _
          ((proEtaleCanonicalTensorComparison g (R.ring V) (R.ring U)
            (R.pull g) aV aU).hom.app ((push R g).obj M, L) ≫
            aU.tensor.map (Prod.mkHom
              ((proEtaleRingDerivedAdjunction g (R.ring V) (R.ring U)
                (R.pull g)).counit.app M) (𝟙 _)))) ≫
      (properComparison a g).app (aU.tensor.obj (M, (pull R g).obj L)) ≫
      (push S g).map ((scalarTensor (a.map U) aU bU).hom.app
        (M, (pull R g).obj L) ≫
        bU.tensor.map (Prod.mkHom (𝟙 _) ((scalarPull a g).hom.app L))) =
    (scalarTensor (a.map V) aV bV).hom.app ((push R g).obj M, L) ≫
      bV.tensor.map (Prod.mkHom ((properComparison a g).app M) (𝟙 _)) ≫
      (proEtaleRingDerivedAdjunction g (S.ring V) (S.ring U) (S.pull g)).homEquiv _ _
        ((proEtaleCanonicalTensorComparison g (S.ring V) (S.ring U)
          (S.pull g) bV bU).hom.app
            ((push S g).obj ((pbcDerivedExtend (a.map U)).obj M),
              (pbcDerivedExtend (a.map V)).obj L) ≫
          bU.tensor.map (Prod.mkHom
            ((proEtaleRingDerivedAdjunction g (S.ring V) (S.ring U)
              (S.pull g)).counit.app ((pbcDerivedExtend (a.map U)).obj M)) (𝟙 _))) := by
  rw [proper_coefficient_mate]
  exact tensor_mate_coherence
    (proEtaleRingDerivedAdjunction g (R.ring V) (R.ring U) (R.pull g))
    (proEtaleRingDerivedAdjunction g (S.ring V) (S.ring U) (S.pull g))
    aV.tensor aU.tensor bV.tensor bU.tensor
    (proEtaleCanonicalTensorComparison g (R.ring V) (R.ring U)
      (R.pull g) aV aU).hom
    (scalarTensor (a.map V) aV bV).hom
    (scalarTensor (a.map U) aU bU).hom
    (proEtaleCanonicalTensorComparison g (S.ring V) (S.ring U)
      (S.pull g) bV bU).hom
    (scalarPull a g).symm
    (scalarPull_tensor_coefficient_coherence a g aU aV bU bV) M L

/-- Coefficient change preserves the ordinary proper-counit/open projection composite.
No constructibility, projection invertibility, or completeness assumption occurs.

Source: Stacks Project, Tags 07A4, 0D6D, 0E48 and 0E8I; blueprint
`fix-prop-projection-formula.proof.md`, actual-map reduction, step 3
(blueprint: lem-pur-compact-support-projection-coefficient-change).

Proof: expand `projectionMap` using the two defining equations of
`projectionComparisons_existsUnique`, and expand the compact-support comparison
using `comparison_factorization`. For the proper factor transpose under the target
geometric adjunction. The counit equation of the coefficient mate identifies the
transpose with scalar extension of the original counit after the scalar/pullback
comparison. The canonical scalar/pullback tensor square commutes: on flat K-flat
representatives both composites send a pure tensor to the same balanced tensor;
localization and tensor descent give the equality for every pair. Equivalently this
is `ringedExchangeTensorCoherence` for the coefficient square, which requires no
flatness or Cartesian hypothesis. For the open factor transpose under open
extension/restriction. The open-unit normalization makes both restrictions the same
canonical tensor/pullback comparison; extension by zero is fully faithful, giving
equality. The pullback-composition comparisons commute with scalar change by
uniqueness of the composite left adjoint. Paste the proper and open squares using
naturality. This gives exactly the displayed equation, with no cancellation of a
projection morphism. Identity changes give naturality, zero inputs give zero maps,
and quotient coefficient maps require no flatness. -/
theorem compactSupportProjectionCoefficientChange
    {R S : Coefficients.{u}} (a : Change R S)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (aX : ProEtaleTensorModel X (R.ring X))
    (aZ : ProEtaleTensorModel c.Z (R.ring c.Z))
    (aY : ProEtaleTensorModel Y (R.ring Y))
    (bX : ProEtaleTensorModel X (S.ring X))
    (bZ : ProEtaleTensorModel c.Z (S.ring c.Z))
    (bY : ProEtaleTensorModel Y (S.ring Y))
    (hR : R.pull (c.i ≫ c.g) = proEtaleRingCompositeCoefficients c.i c.g
      (R.ring Y) (R.ring c.Z) (R.ring X) (R.pull c.g) (R.pull c.i))
    (hS : S.pull (c.i ≫ c.g) = proEtaleRingCompositeCoefficients c.i c.g
      (S.ring Y) (S.ring c.Z) (S.ring X) (S.pull c.g) (S.pull c.i))
    (K : DerivedCategory (pbcModules X (R.ring X)))
    (L : DerivedCategory (pbcModules Y (R.ring Y))) :
    (pbcDerivedExtend (a.map Y)).map
        (((projectionMap R c aX aZ aY hR).app K).app L) ≫
      (comparison a c).app (aX.tensor.obj (K, (pull R f).obj L)) ≫
      (image S c).map ((scalarTensor (a.map X) aX bX).hom.app
        (K, (pull R f).obj L) ≫
        bX.tensor.map (Prod.mkHom (𝟙 _) ((scalarPull a f).hom.app L))) =
    (scalarTensor (a.map Y) aY bY).hom.app ((image R c).obj K, L) ≫
      bY.tensor.map (Prod.mkHom ((comparison a c).app K) (𝟙 _)) ≫
      (((projectionMap S c bX bZ bY hS).app
        ((pbcDerivedExtend (a.map X)).obj K)).app
          ((pbcDerivedExtend (a.map Y)).obj L)) := by
  let J := (openExtension R c.i).mapDerivedCategory
  let JB := (openExtension S c.i).mapDerivedCategory
  let CY := pbcDerivedExtend (a.map Y)
  let CZ := pbcDerivedExtend (a.map c.Z)
  let CX := pbcDerivedExtend (a.map X)
  let M := J.obj K
  let H := aX.tensor.obj (K, (pull R f).obj L)
  let N := aZ.tensor.obj (M, (pull R c.g).obj L)
  let LB := CY.obj L
  let MB := CZ.obj M
  let KB := CX.obj K
  let dR := (projectionComparisons_existsUnique R c aX aZ aY hR).exists.choose
  let dS := (projectionComparisons_existsUnique S c bX bZ bY hS).exists.choose
  let pR := (proEtaleRingDerivedAdjunction c.g (R.ring Y) (R.ring c.Z)
    (R.pull c.g)).rightAdjointProjectionMap dR.tensorPullback.hom
  let pS := (proEtaleRingDerivedAdjunction c.g (S.ring Y) (S.ring c.Z)
    (S.pull c.g)).rightAdjointProjectionMap dS.tensorPullback.hom
  let pi : aY.tensor.obj ((push R c.g).obj M, L) ⟶ (push R c.g).obj N :=
    (pR.app M).app L
  let piB : bY.tensor.obj ((push S c.g).obj MB, LB) ⟶
      (push S c.g).obj (bZ.tensor.obj (MB, (pull S c.g).obj LB)) :=
    (pS.app MB).app LB
  let piBO : bY.tensor.obj ((push S c.g).obj (JB.obj KB), LB) ⟶
      (push S c.g).obj (bZ.tensor.obj (JB.obj KB, (pull S c.g).obj LB)) :=
    (pS.app (JB.obj KB)).app LB
  let gamma : N ⟶ J.obj H := (projectionOpenFactor R c aX aZ hR K L).hom
  let gammaB := (projectionOpenFactor S c bX bZ hS KB LB).hom
  let qg : CZ.obj N ⟶ bZ.tensor.obj (MB, (pull S c.g).obj LB) :=
    (scalarTensor (a.map c.Z) aZ bZ).hom.app (M, (pull R c.g).obj L) ≫
    bZ.tensor.map (Prod.mkHom (𝟙 _) ((scalarPull a c.g).hom.app L))
  let qf : CX.obj H ⟶ bX.tensor.obj (KB, (pull S f).obj LB) :=
    (scalarTensor (a.map X) aX bX).hom.app (K, (pull R f).obj L) ≫
    bX.tensor.map (Prod.mkHom (𝟙 _) ((scalarPull a f).hom.app L))
  have ht : CY.map pi ≫ (properComparison a c.g).app N ≫ (push S c.g).map qg =
      (scalarTensor (a.map Y) aY bY).hom.app ((push R c.g).obj M, L) ≫
        bY.tensor.map (Prod.mkHom ((properComparison a c.g).app M) (𝟙 _)) ≫ piB := by
    dsimp only [pi, piB, pR, pS]
    simp only [Adjunction.rightAdjointProjectionMap_app_app]
    rw [dR.tensorPullback_eq, dS.tensorPullback_eq]
    exact proper_projection_coefficient_square a c.g aZ aY bZ bY M L
  have ho : CZ.map gamma ≫ (openComparison a c.i).app H ≫ JB.map qf =
      qg ≫ bZ.tensor.map (Prod.mkHom ((openComparison a c.i).app K) (𝟙 _)) ≫
        gammaB := by
    dsimp only [qg, qf, gamma, gammaB, M, H, N, LB, MB, KB, CY, CZ, CX, J, JB]
    simpa only [Functor.comp_obj, Category.assoc] using
      openProjectionFactor_coefficient_change a c aX aZ bX bZ hR hS K L
  have hp : ((projectionMap R c aX aZ aY hR).app K).app L =
      pi ≫ (push R c.g).map gamma := by
    change pi ≫ (push R c.g).map ((dR.openProjection.hom.app K).app L) = _
    rw [dR.openProjection_eq]
  have hpB : ((projectionMap S c bX bZ bY hS).app KB).app LB =
      piBO ≫ (push S c.g).map gammaB := by
    change piBO ≫
      (push S c.g).map ((dS.openProjection.hom.app KB).app LB) = _
    rw [dS.openProjection_eq]
  have hn := (properComparison a c.g).naturality gamma
  change CY.map ((push R c.g).map gamma) ≫ (properComparison a c.g).app (J.obj H) =
    (properComparison a c.g).app N ≫ (push S c.g).map (CZ.map gamma) at hn
  rw [hp, comparison_factorization, comparison_factorization, hpB]
  change CY.map (pi ≫ (push R c.g).map gamma) ≫
      ((properComparison a c.g).app (J.obj H) ≫
        (push S c.g).map ((openComparison a c.i).app H)) ≫
      (push S c.g).map (JB.map qf) =
    (scalarTensor (a.map Y) aY bY).hom.app ((push R c.g).obj M, L) ≫
      bY.tensor.map (Prod.mkHom
        ((properComparison a c.g).app M ≫
          (push S c.g).map ((openComparison a c.i).app K)) (𝟙 LB)) ≫
      (piBO ≫ (push S c.g).map gammaB)
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn]
  rw [← (push S c.g).map_comp_assoc, ← (push S c.g).map_comp]
  simp only [Category.assoc]
  rw [ho]
  simp only [Functor.map_comp]
  rw [reassoc_of% ht]
  have hnB := NatTrans.congr_app (pS.naturality ((openComparison a c.i).app K)) LB
  change bY.tensor.map (Prod.mkHom
      ((push S c.g).map ((openComparison a c.i).app K)) (𝟙 LB)) ≫
      piBO =
    piB ≫ (push S c.g).map
      (bZ.tensor.map (Prod.mkHom ((openComparison a c.i).app K) (𝟙 _))) at hnB
  erw [← reassoc_of% hnB]
  rw [← bY.tensor.map_comp_assoc]
  rfl

end WeilConjectures.PurCompactSupport
