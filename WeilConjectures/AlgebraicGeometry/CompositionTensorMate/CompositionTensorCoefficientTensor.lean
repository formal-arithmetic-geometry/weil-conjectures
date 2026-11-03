/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompositionTensorMate.CondensedBridge.CompositionTensorMateData2

/-! # Tensor generators in normalized finite coefficient coordinates -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CompositionTensorMate

open FiniteDiscreteOrdinary CondensedBridge
variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [Finite A] [DiscreteTopology A]
variable [UpperStarPreservesFlat (ModuleCat.{u + 1} (ULift.{u + 1} A))]

/-- The specified coefficient encoding preserves the actual compactification projection
and its exceptional tensor mate, with the signed symmetry and coefficient unit retained.
Source: composition proof Step 2
(blueprint: lem-pur-composition-tensor-coefficient-tensor).

Proof: use the all-input inverse-encoding projection square at the two encoded native
objects. Apply the forward equivalence, use projection naturality at the equivalence
unit, and cancel the equivalence unit and counit. Their monoidal equations identify
the inverse tensorators, and the definitions of inverseCompactEncoding and
inverseEncodingPull give exactly the compactSupport and pullback components displayed
here. The exchangeProjectionData projection equals this compactification projection
by its proper/open factorization. For theta, the object comparison sends the finite-Tor
input into the ordinary constructible finite-Tor category. Pullback preserves that
class, the exceptional image of the unit has a bounded-below etale origin, and finite
Tor amplitude bounds the tensor source below. Thus both standing Hom guards hold.
Apply the Hom normalization to the native defining transpose. Naturality of the
support comparison, preservation of the specified Koszul symmetry, and the projection
square transfer its first two factors. Conjugation by isomorphisms preserves the
invertibility predicate, so inverseOnDomain transfers even in the noninvertible case.
The counit comparison, monoidal left-unitor equation and the coefficient unit then
identify the remaining factors. Standing Hom naturality transfers the source and
unit maps, yielding the displayed theta equation with omegaComparison. -/
theorem compositionTensorCoefficientTensor (E : ∀ T : Scheme.{u}, Encoding A T)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    [CompactSpace Y] :
    (∀ (M : Native A X) (K : Native A Y),
    letI := FiniteNativeTensor.encodingMonoidal A X (E X)
    letI := FiniteNativeTensor.encodingMonoidal A Y (E Y)
    (Functor.Monoidal.μIso (N A E Y) ((nativeSupport A f).obj M) K).hom ≫
      (N A E Y).map (nativeProjection A f M K) ≫
      (canonicalSupport A E f).hom.app (M ⊗ (nativePull A f).obj K) ≫
      (F (ULift.{u + 1} A) f).map
        ((Functor.Monoidal.μIso (N A E X) M ((nativePull A f).obj K)).inv ≫
          (N A E X).obj M ◁ (FiniteNativeTensor.encodingDerivedPull A E f).inv.app K) =
    (canonicalSupport A E f).hom.app M ▷ (N A E Y).obj K ≫
      ((projectionMap (ModuleCat.{u + 1} (ULift.{u + 1} A)) f).app
        ((N A E X).obj M)).app ((N A E Y).obj K)) ∧
    (∀ K : Native A Y,
    CondensedRing.condensedConstructibleFiniteTor (coefficient A) Y K →
    letI := FiniteNativeTensor.encodingMonoidal A X (E X)
    (N A E X).map (nativeTheta A E f K) ≫ (exceptionalComparison A E f K).hom =
      (Functor.Monoidal.μIso (N A E X) ((nativePull A f).obj K)
        (nativeOmega A E f)).inv ≫
        ((FiniteNativeTensor.encodingDerivedPull A E f).inv.app K ⊗ₘ
          (omegaComparison A E f).hom) ≫ theta (ULift.{u + 1} A) f ((N A E Y).obj K)) := by
  sorry

end AlgebraicGeometry.ProEtale.CompositionTensorMate
