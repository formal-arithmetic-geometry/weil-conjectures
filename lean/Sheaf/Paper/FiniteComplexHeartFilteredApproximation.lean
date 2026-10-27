/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NL
-/
module

public import Sheaf.Paper.FiniteConstructibleComplexHeartPresentations
public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedQcqsPushforwardContinuity
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Sheaf.Paper.NoetherianFiniteComplexHeartFilteredClosure
import Sheaf.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian

/-!
# Closure of filtered finite-complex heart presentations

Source: blueprint latest, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-refinement.proof.md, (2), first paragraph; Noetherian heart
argument in sk-prop-ind-heart/sk-prop-ind-heart.proof.md
(blueprint: lem-sfb-finite-complex-heart-filtered-approximation).

The node's six continuous coefficient cases are written explicitly: the recorded
localizing-admissibility predicate additionally permits finite-subextension-valued
algebraic-closure coefficients, which are not part of this assertion.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The filtered finite-complex heart class contains zero and the constructible modules
and is closed under all ambient kernels, cokernels, extensions and small coproducts.
The local cohomology hypothesis concerns the actual uncompleted derived functor of
module global sections. No finite-stage lift of a map or extension is assumed.

Source: blueprint latest, det-sf-comp-coherence-refinement.proof.md, (2), first paragraph,
and sk-prop-ind-heart.proof.md, Noetherian heart argument. Compare Hemo--Richarz--Scholbach,
Section 8, (8.1), Lemmas 5.3 and 8.6, and Proposition 8.2; an exact reference for the full
coefficient generality is WANTED
(blueprint: lem-sfb-finite-complex-heart-filtered-approximation).

Apply `noetherian_finite_complex_heart_filtered_closure` to the same coefficient
object and scheme. It gives exactly the six asserted closure properties for every
Noetherian scheme, without requiring affineness or the local cohomology bound.
Its proof follows the Noetherian constructible-heart and FP2 hull argument of
sk-prop-ind-heart.proof.md. The finite complexes, ambient module maps, indexing
universe, and six coefficient alternatives are identical in both statements.
-/
theorem finite_complex_heart_filtered_approximation
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ :
      (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
          (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
        Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
          Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))))
    (X : Scheme.{u}) [IsAffine X] [IsLocallyNoetherian X] [CompactSpace X]
    (c : ℕ)
    (hcd : ∀ (K : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) ℤ),
      IsFiniteConstantConstructibleComplex Λ X K →
      ∀ (U : X.ProEt) [IsAffine U.left] (q : ℤ), (c : ℤ) < q →
        IsZero ((DerivedCategory.homologyFunctor Ab.{u + 1} q).obj
          ((condensedModuleSections Λ U.left).rightDerivedFunctor.obj
            ((DerivedCategory.singleFunctor _ 0).obj
              ((CondensedRing.upperStar Λ U.hom).obj (K.homology 0)))))) :
    (indFiniteConstructibleComplexHearts Λ X).ContainsZero ∧
    IsConstantModelConstructible Λ X ≤ indFiniteConstructibleComplexHearts Λ X ∧
    (indFiniteConstructibleComplexHearts Λ X).IsClosedUnderKernels ∧
    (indFiniteConstructibleComplexHearts Λ X).IsClosedUnderCokernels ∧
    (indFiniteConstructibleComplexHearts Λ X).IsClosedUnderExtensions ∧
    ∀ I : Type (u + 1),
      (indFiniteConstructibleComplexHearts Λ X).IsClosedUnderColimitsOfShape (Discrete I) := by
  have _ := hcd
  exact noetherian_finite_complex_heart_filtered_closure ℓ Λ hΛ X

end AlgebraicGeometry.ProEtale
