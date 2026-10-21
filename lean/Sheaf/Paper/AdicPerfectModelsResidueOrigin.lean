/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2
-/
module

public import Sheaf.Paper.AdicStratifiedPerfectData


/-! # Completeness, bounds and etale residue origin from perfect local models

Source: Bhatt--Scholze, Proposition 6.6.11, reverse implication, and Lemma 6.5.3.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme

/-- Stratified perfect models give global completeness and bounds, and bounded
constructible etale origin of the residue. The Tor condition is deliberately separate:
it follows from field-valued tensor exactness.
Source: Bhatt--Scholze, Proposition 6.6.11, reverse implication, and Lemma 6.5.3
(blueprint: lem-sfb-adic-perfect-models-residue-origin).

Proof: On each model cover, transport the given finite-projective complex to the small
site and apply adicPerfectModel_complete_reduction. It gives completeness and vanishing
of both the model and its residue outside the termwise bounds; the residue cohomology
is the constant realization of finite-dimensional coefficient cohomology. Restriction
along the stratum immersion and then to the slice commutes with this calculation by
the finite-projection scalar comparisons. Detect completeness by
adicStratumCompletionUnit_detection. For bounds, choose finitely many quasi-compact
pieces of the covering schemes over each of the finitely many Noetherian strata, and
take the minimum of their lower bounds and maximum of their upper bounds. Exact
restriction commutes with cohomology and finite-stratum detection proves the global
vanishing, for K and its residue separately. This is
exists_global_bounds_of_stratified_local_bounds. If the selected family is empty, use
[0,0] and the empty-cover sheaf axiom. The residue cohomology is intrinsically
constructible on the given strata, with finite-dimensional, hence finitely presented,
constant module values. Noetherian global constructibility and the bounded derived
constructible comparison equivalence descend this bounded residue to an etale complex
C. Exact fully faithful comparison identifies its cohomology, bounds and the required
residue isomorphism. Fixed-scalar restriction and the small-site equivalences give the
stated presentation without changing the coefficients or the quotient projection. -/
theorem adicPerfectModels_residueOrigin (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (hI : I.IsMaximal ∧ ∀ J : Ideal A, J.IsMaximal → J = I)
    [IsAdicComplete I A]
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)))
    (hK : IsSfbStratifiedPerfect X I K) :
    IsSfbAdicComplete X I K ∧
      (∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, (q < a ∨ b < q) →
        IsZero ((DerivedCategory.homologyFunctor _ q).obj K)) ∧
      ∃ C : CochainComplex
          (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1)))) ℤ,
        (∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, (q < a ∨ b < q) → IsZero (C.homology q)) ∧
        (∀ q : ℤ, IsConstructibleSheaf (C.homology q)) ∧
        Nonempty (DerivedCategory.Q.obj (sfbResidueComplex X I K) ≅
          DerivedCategory.Q.obj
            (((ProEtale.comparisonUpperStar
              (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))) X).mapHomologicalComplex
                (.up ℤ)).obj C)) := by
  sorry

end AlgebraicGeometry.Scheme
