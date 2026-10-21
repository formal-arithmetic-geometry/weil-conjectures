/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N5
-/
module

public import Sheaf.Paper.LocalizingAdmissibleCoefficients
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.Paper.CondensedConstantConstructibility
public import Sheaf.Paper.CondensedAmbientExchange
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.Paper.KFlatScalarComparisonNormalization
import Sheaf.Paper.FiniteDiscreteOrdinaryEquivalence
import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison
import Sheaf.Paper.FiniteLevelProEtaleBaseChange
import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
import Sheaf.CategoryTheory.ExactEquivalenceDerivedSquares
import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Sheaf.Algebra.Homology.RoosConeCalculus
import Sheaf.Paper.DerivedNakayamaFirstReduction
import Sheaf.CategoryTheory.PastedMatesCounitNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift
import Sheaf.CategoryTheory.ExactDerivedComposition
import Sheaf.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import Sheaf.CategoryTheory.ModuleObjects.LiftExact
import Sheaf.AlgebraicGeometry.QcqsProperLocalizingCoproducts
import Sheaf.CategoryTheory.Triangulated.LocalizingIsoLocus
import Sheaf.AlgebraicGeometry.ProEtaleRingedClosedCounit
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Topology.Constructible

/-! # Closed proper base change on bounded constructible finite-Tor inputs

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-sf-comp-coherence,
det-sf-comp-coherence-refinement.proof.md, (2), proper base change along the closed
complement (blueprint: lem-sfb-qcqs-proper-constructible-closed-base-change).

The exchange is the actual unit--square--counit mate on ordinary unbounded internal module
objects. The coefficient predicate retains exactly the node's norm-topological convention.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- The six coefficient families with the discrete or induced norm-topological convention.

Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-localizing-closure,
coefficient convention, restricted to the exact list in the present theorem
(blueprint: lem-sfb-qcqs-proper-constructible-closed-base-change). -/
def IsNormTopologicalLocalizingAdmissibleCoefficient (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] : Prop :=
  (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
    Finite A ∧ (∃ n : ℕ, ∀ a : A, (ℓ ^ n) • a = 0) ∧
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E))) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj (PadicAlgCl ℓ)))

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Closed proper base change over any qcqs base, on bounded constructible complexes of
finite Tor amplitude, for the discrete or induced ell-adic admissible coefficient list.

Source: blueprint main-20261015, det-sf-comp-coherence-refinement.proof.md, (2), the
closed-complement calculation on the bounded constructible finite-Tor generator
(blueprint: lem-sfb-qcqs-proper-constructible-closed-base-change).

Proof plan, following the six steps of the DAG node:
1. Properness makes X and Y qcqs; the closed subschemes and the base-changed proper
   morphism remain qcqs. Constructible closed inverse image preserves finite constant
   scalar models and finite Tor amplitude, by the scalar/pullback comparison and closed
   counit (lem-sfb-kflat-scalar-comparison-normalization and
   lem-weil-pbc-proetale-ringed-closed-counit). For finite discrete coefficients, use
   lem-sf-module-object-ordinary-coefficient-equivalence and sk-thm-pe-constructible-comparison
   to obtain an etale-origin witness. thm-weil-pbc-finite-level-proetale proves the exchange
   invertible. lem-sfb-internal-module-operations-transport and
   lem-derived-exact-equivalence-squares identify the actual normalized mate.
2. For integral coefficients, lem-sfb-qcqs-integral-finite-model-completeness gives complete
   inputs with classical finite reductions. lem-sfb-integral-ambient-tower-comparison makes
   ordinary direct images complete. Closed inverse image is exact and preserves products
   (lem-weil-pbc-proetale-immersion-limit-preservation), hence preserves the strict Roos
   complex and its augmentation (lem-pe-roos-cone-calculus), and the two-term quotient
   resolutions. Both exchange endpoints are therefore complete.
3. lem-sfb-integral-quotient-exchange-comparison identifies the reduced actual exchange
   with finite-coefficient exchange. Apply step 1, then
   det-pe-derived-nakayama-first-reduction through the exact internal/section equivalences
   to conclude integral invertibility.
4. For rational coefficients use the integral scalar-extension generators from
   lem-sfb-qcqs-rational-integral-localizing-generators. The two scalar projection maps
   are invertible by lem-sfb-qcqs-proper-integral-rational-scalar-comparison. The square
   comparing integral and rational exchange commutes: transpose both composites by the
   base-changed adjunction, use lem-sfb-pasted-mates-counit-normalization to cancel units,
   and use scalar/pullback coherence to identify the common transpose. Thus step 3 implies
   invertibility on every scalar-extension generator.
5. Exact pullback and triangulated ordinary direct image carry canonical shifts. The
   canonical derived adjunction has shift-compatible unit and counit by
   lem-sp-canonical-right-derived-adjunction-shift. The exact-derived composition and
   natural-isomorphism comparisons are induced termwise, so commute with shifts, including
   the signs in differentials. The composite mate therefore commutes with shifts and the
   connecting maps of distinguished triangles.
6. On the localizing hull, lem-sfb-qcqs-proper-localizing-coproducts applies to f over S
   and to its base change over C. Pullback preserves the input classes by step 1 and
   preserves coproducts as a left adjoint. det-sf-determination-localizing makes the
   isomorphism locus localizing. It contains the integral scalar-extension generators
   by step 4, and hence every rational bounded constructible finite-Tor input by the
   generation lemma. Together with steps 1--3 this covers the exact coefficient list,
   including all continuous norm-topological algebraic-closure sections. -/
theorem qcqs_proper_constructible_closed_baseChange
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : IsNormTopologicalLocalizingAdmissibleCoefficient ℓ Λ)
    {S X Y C : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
    (q : Y ⟶ S) [IsProper q] (f : X ⟶ Y) [IsProper f]
    (c : C ⟶ Y) [IsClosedImmersion c]
    [QuasiCompact (Scheme.Opens.ι (X := Y)
      ⟨(Set.range c)ᶜ, c.isClosedEmbedding.isClosed_range.isOpen_compl⟩)]
    (L : ConstantModelConstructibleFiniteTor Λ X) :
    IsIso ((condensedAmbientExchange Λ
      (g' := pullback.fst f c) (f' := pullback.snd f c) (f := f) (g := c)
      { w := pullback.condition
        isoPullback := Iso.refl _
        hom_fst := Category.id_comp _
        hom_snd := Category.id_comp _ }).app L.obj) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
