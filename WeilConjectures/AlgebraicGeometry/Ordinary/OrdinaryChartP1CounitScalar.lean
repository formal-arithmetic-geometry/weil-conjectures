/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartUnitScalar
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryChartTateScalar
import all WeilConjectures.AlgebraicGeometry.P1.P1CounitScalar
import all WeilConjectures.AlgebraicGeometry.VectorTraceScalar.VectorTraceScalarDescent
import WeilConjectures.AlgebraicGeometry.Etale.EtaleDirectScalarProjection

/-! # Unbounded scalar compatibility of the normalized projective-line counit

Source: blueprint smooth-purity reduction, Charts.
(blueprint: lem-pur-ordinary-chart-p1-counit-scalar).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  derivedTensor upperStar lowerStar
  projectiveLineTraceDatum projectiveLineTraceTransport
  AlgebraicGeometry.Etale.purityScalarSingleMap
  AlgebraicGeometry.Etale.purityScalarUnitMap
  ExceptionalCoefficients.tensorIso ExceptionalCoefficients.unitIso
  singleFunctorObjUnitIso derivedTensorRightUnitor
  HasDerivedCategory.ofIsGrothendieckAbelian HasDerivedCategory.ofHasKInjectiveResolutions
  _root_.DerivedCategory.singleFunctors

private theorem balanced_projection_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : DerivedCategoryModule A Y)
    (L : DerivedCategoryModule A X) (L' : DerivedCategoryModule B X)
    (l : (scalarExtension φ X).obj L ⟶ L') :
    (scalarExtension φ Y).map (ordinaryFiniteProjection A f L K) ≫
      (scalarMate φ f).app
        (((ordinaryFiniteTensor A X).obj ((ordinaryFinitePullback A f).obj K)).obj L) ≫
      (ordinaryFinitePushforward B f).map
        ((ExceptionalCoefficients.tensorIso φ X).hom.app
            ((ordinaryFinitePullback A f).obj K, L) ≫
          ((ordinaryFiniteTensor B X).map ((scalarPullbackIso φ f).inv.app K)).app
            ((scalarExtension φ X).obj L) ≫
          ((ordinaryFiniteTensor B X).obj
            ((ordinaryFinitePullback B f).obj ((scalarExtension φ Y).obj K))).map l) =
    (ExceptionalCoefficients.tensorIso φ Y).hom.app
        (K, (ordinaryFinitePushforward A f).obj L) ≫
      ((ordinaryFiniteTensor B Y).obj ((scalarExtension φ Y).obj K)).map
        ((scalarMate φ f).app L ≫ (ordinaryFinitePushforward B f).map l) ≫
      ordinaryFiniteProjection B f L' ((scalarExtension φ Y).obj K) := by
  have h := etaleDirectScalarProjection φ f K L
  have hn := (orderedDirectProjectionNat B f ((scalarExtension φ Y).obj K)).naturality l
  have hn' : ((ordinaryFiniteTensor B Y).obj ((scalarExtension φ Y).obj K)).map
      ((ordinaryFinitePushforward B f).map l) ≫
      orderedDirectProjection B f ((scalarExtension φ Y).obj K) L' =
    orderedDirectProjection B f ((scalarExtension φ Y).obj K)
      ((scalarExtension φ X).obj L) ≫
      (ordinaryFinitePushforward B f).map
        (((ordinaryFiniteTensor B X).obj
          ((ordinaryFinitePullback B f).obj ((scalarExtension φ Y).obj K))).map l) := by
    simpa only [Functor.comp_map, orderedDirectProjection, ordinaryFiniteTensor,
      ordinaryFinitePullback, ordinaryFinitePushforward, rightDerivedLowerStar] using hn
  have hh := congrArg (fun z ↦ z ≫ (ordinaryFinitePushforward B f).map
    (((ordinaryFiniteTensor B X).obj
      ((ordinaryFinitePullback B f).obj ((scalarExtension φ Y).obj K))).map l)) h
  simp only [Category.assoc, ordinaryFinitePushforward, ordinaryFiniteTensor,
    ordinaryFinitePullback] at hn' hh
  rw [← hn'] at hh
  simpa only [orderedDirectProjection_eq, ordinaryFiniteProjection,
    ordinaryFinitePushforward, ordinaryFiniteTensor, ordinaryFinitePullback,
    rightDerivedLowerStar, Functor.map_comp, Category.assoc] using hh

private theorem datum_trace_scalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (tA : OrdinaryFiniteTwistTransport A N hA)
    (tB : OrdinaryFiniteTwistTransport B N hB)
    (DA : OrdinaryFiniteP1Datum A N hA tA S hS)
    (DB : OrdinaryFiniteP1Datum B N hB tB S hS) :
    (scalarMate φ (ProjectiveLine S ↘ S)).app
        ((ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧) ≫
      (ordinaryFinitePushforward B (ProjectiveLine S ↘ S)).map
        (ProEtale.reductionEtaleShiftedLineIso φ (ProjectiveLine S) N hA hB
          (ordinaryFiniteP1_isUnit N S hS)).hom ≫ DB.trace =
    (scalarExtension φ S).map DA.trace ≫ VectorTraceScalar.unit φ S := by
  obtain rfl := ordinaryFiniteTwistTransport_unique A N hA tA
    (projectiveLineTraceTransport N hN A hA)
  obtain rfl := ordinaryFiniteTwistTransport_unique B N hB tB
    (projectiveLineTraceTransport N hN B hB)
  obtain rfl := ordinaryFiniteP1Datum_unique A N hA _ S hS DA
    (projectiveLineTraceDatum N hN A hA S hS)
  obtain rfl := ordinaryFiniteP1Datum_unique B N hB _ S hS DB
    (projectiveLineTraceDatum N hN B hB S hS)
  rw [ordinaryChartShiftedLineScalarEq φ N hN]
  have h := VectorTraceScalar.projective_trace_square N hN φ hA hB S hS
  simpa only [VectorTraceScalar.projective, OrdinaryFiniteP1Datum.trace, Category.assoc]
    using h

/-- Unbounded scalar compatibility of the normalized projective-line counit.
Source: blueprint smooth-purity reduction, Charts.
(blueprint: lem-pur-ordinary-chart-p1-counit-scalar).

Proof: Use uniqueness of normalized twist transport and P1 data to identify their trace maps with
the canonical projective-line trace. The normalized shifted Tate scalar equality and the
vector-trace coefficient square give the trace coefficient equation.
The coefficient projection formula and its naturality move the input tensor factor and the shifted
Tate scalar map across direct image. Properness makes the projection map invertible.
Use the generic tensor-trace counit pasting identity, the prescribed counit normalizations and the
transported single-unit coefficient square. This yields the actual P1 counit square on the
arbitrary input. -/
theorem ordinaryChartP1CounitScalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (tA : OrdinaryFiniteTwistTransport A N hA)
    (tB : OrdinaryFiniteTwistTransport B N hB)
    (DA : OrdinaryFiniteP1Datum A N hA tA S hS)
    (DB : OrdinaryFiniteP1Datum B N hB tB S hS)
    (K : DerivedCategoryModule A S) :
    (scalarMate φ (ProjectiveLine S ↘ S)).app
        ((ordinaryFiniteP1Right A N hA S).obj K) ≫
      (ordinaryFinitePushforward B (ProjectiveLine S ↘ S)).map
        (ProEtale.reductionEtaleP1ScalarIso φ S N hA hB hS K).hom ≫
      DB.adjunction.counit.app ((scalarExtension φ S).obj K) =
    (scalarExtension φ S).map (DA.adjunction.counit.app K) := by
  let q := ProjectiveLine S ↘ S
  let LA := (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧
  let LB := (ordinaryFiniteLine B N hB (ProjectiveLine S))⟦(2 : ℤ)⟧
  let l := (ProEtale.reductionEtaleShiftedLineIso φ (ProjectiveLine S) N hA hB
    (ordinaryFiniteP1_isUnit N S hS)).hom
  let KB := (scalarExtension φ S).obj K
  have : IsLocallyNoetherian (ProjectiveLine S) :=
    LocallyOfFiniteType.isLocallyNoetherian q
  have : CompactSpace (ProjectiveLine S) := QuasiCompact.compactSpace_of_compactSpace q
  have : IsNoetherian (ProjectiveLine S) := ⟨⟩
  have : IsIso (ordinaryFiniteProjection A q LA K) :=
    isIso_proper_projection_formula_reordered A q LA K
  have hπ := balanced_projection_scalar φ q K LA LB l
  simp only [← Category.assoc]
  apply tensor_trace_counit_square (scalarExtension φ S)
    (ordinaryFiniteTensor A S) (ordinaryFiniteTensor B S)
    (ExceptionalCoefficients.tensorIso φ S).hom K
    ((ordinaryFinitePushforward A q).obj LA) (ordinaryFiniteUnit A S)
    ((ordinaryFinitePushforward B q).obj LB) (ordinaryFiniteUnit B S)
    ((ordinaryFinitePushforward A q).obj ((ordinaryFiniteP1Right A N hA S).obj K))
    ((ordinaryFinitePushforward B q).obj ((ordinaryFiniteP1Right B N hB S).obj KB))
    (ordinaryFiniteProjection A q LA K) (ordinaryFiniteProjection B q LB KB)
    ((scalarMate φ q).app ((ordinaryFiniteP1Right A N hA S).obj K) ≫
      (ordinaryFinitePushforward B q).map
        (ProEtale.reductionEtaleP1ScalarIso φ S N hA hB hS K).hom)
    (DA.adjunction.counit.app K) (DB.adjunction.counit.app KB)
    DA.trace DB.trace
    ((scalarMate φ q).app LA ≫ (ordinaryFinitePushforward B q).map l)
    (VectorTraceScalar.unit φ S)
    (derivedTensorSingleUnitIso K).hom (derivedTensorSingleUnitIso KB).hom
  · simpa only [ProEtale.reductionEtaleP1ScalarIso, Iso.trans_hom, Iso.app_hom,
      Functor.mapIso_hom, Iso.prod_hom, Functor.uncurry_obj_map,
      Functor.prod_obj, Iso.symm_hom, Functor.map_comp, Category.assoc,
      ordinaryFiniteP1Right, ordinaryFiniteTwistedPullback, derivedTensorRight,
      ordinaryFiniteTensor,
      ordinaryFinitePullback, Functor.comp_obj,
      Functor.flip_obj_obj, q, LA, LB, l, KB] using hπ
  · exact DA.counit_normalization K
  · exact DB.counit_normalization KB
  · simpa only [q, LA, LB, l, Category.assoc] using
      datum_trace_scalar φ N hN hA hB S hS tA tB DA DB
  · exact ordinaryChartSingleUnitScalarSquare φ S K

end AlgebraicGeometry.Etale
