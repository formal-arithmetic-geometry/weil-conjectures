/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.Paper.AdicExceptionalBase
public import Sheaf.SixFunctors.OpenFactorTensorModel
public import Sheaf.SixFunctors.OpenFactorPullModel
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.IntegralOperationsScalarComparisons

/-! # Representative-normalized presentations for adic projection
Source: Bhatt--Scholze Definition 3.4.10 and Lemma 6.7.14
(blueprint: def-per-adic-exceptional-operation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme Opposite
namespace WeilConjectures.AdicExceptionalProjection

variable {k : Type u} [Field k] (l : ℕ) [Fact l.Prime] [Fact (IsUnit (l : k))]

/-- Conclusions at a single arrow and coefficient field. In particular the right
functors, their preservation and their adjunctions are outputs, not hypotheses.
Source: Lemmas 6.7.2 and 6.7.19 (blueprint: def-per-adic-exceptional-operation). -/
structure Operation (E : Coefficient.{u} l) {X Y : Spaces k} (f : X ⟶ Y)
    (c : Compactification (arrow f)) where
  pullModel : OpenFactorCoherence.Pull l E.carrier (arrow f)
  direct : C l E X ⥤ C l E Y
  directRealization : direct ⋙ (sfIntegralConstructible l E.carrier Y.scheme).ι ≅
    (sfIntegralConstructible l E.carrier X.scheme).ι ⋙
      sfCompletedDerivedDirectImage l E.carrier (arrow f)
  directCoefficients : sfCompletedModuleDirectImage l E.carrier (arrow f) ≅
    proEtaleRingModuleDirectImage (arrow f)
      ((PurCompactSupport.completed l E.carrier).ring Y.scheme)
      ((PurCompactSupport.completed l E.carrier).ring X.scheme)
      ((PurCompactSupport.completed l E.carrier).pull (arrow f))
  directCoefficientSections : ∀ (N : scalarReductionSource l E.carrier X.scheme)
    (U : Y.scheme.ProEt) (x : N.val.obj (op ((proEtaleBaseChange (arrow f)).obj U))),
    (directCoefficients.hom.app N).val.app (op U) x = x
  ordinary : ExactAdjunction l E Y X (pull l E f) direct
  ordinaryShift : ordinary.leftShift = pullShift l E f
  ordinaryNormalization : ∀ (M : C l E Y) (K : C l E X)
    (a : (pull l E f).obj M ⟶ K),
    (ordinaryRingAdj l E f).homEquiv M.obj K.obj
      ((OpenFactorCoherence.Pull.unit l E.carrier pullModel).app M.obj ≫ a.hom) =
      (ordinary.adj.homEquiv M K a).hom ≫ directRealization.hom.app K ≫
        (Functor.rightDerivedFunctorNatIso directCoefficients).hom.app K.obj
  exceptional : C l E Y ⥤ C l E X
  shriek : ExactAdjunction l E X Y (support l E f c) exceptional
  supportShift : shriek.leftShift = AdicExceptionalProjection.supportShift l E f c
  reduction : ∀ n : ℕ,
    exceptional ⋙ red l E X n ≅ red l E Y n ⋙ finiteExceptional l E f c n
  finiteBounded : ∀ n : ℕ, letI := c.hasCompactification
    Etale.HasBoundedBelowUpperShriek (ModuleCat.{u + 1}
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E.carrier (n + 1)))) (arrow f)
  reductionPlus : ∀ (M : C l E Y) (n : ℕ),
    DerivedCategory.TStructure.t.plus
      ((sfIntrinsicDerivedEquivalence Y.scheme
        (Padic.coefficientExtensionRing l E.carrier (n + 1))).inverse.obj
          ((red l E Y n).obj M))
  counitReduction : ∀ (M : C l E Y) (n : ℕ),
    (scalarReductionDerivedExtension l E.carrier Y.scheme n).map
        (shriek.adj.counit.app M).hom =
      (sfCompactSupportFiniteReductionIso l k Fact.out c E.carrier
        (exceptional.obj M) n).hom ≫
      (sfAmbientCompactSupportCandidate
        (Padic.coefficientExtensionRing l E.carrier (n + 1)) c).map
          ((reduction n).hom.app M) ≫
      finiteCounit l E f c n (finiteBounded n) ((red l E Y n).obj M) (reductionPlus M n)

end WeilConjectures.AdicExceptionalProjection
