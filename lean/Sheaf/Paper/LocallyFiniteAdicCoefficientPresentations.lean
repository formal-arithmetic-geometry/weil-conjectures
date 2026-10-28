/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E7
-/
module

public import Sheaf.Paper.LocallyFiniteAdicRealizationData

/-! # Coefficient and section transport for the native adic realization

Source: Bhatt--Scholze, Lemma 6.8.2 and Proposition 6.8.14.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option linter.all false

attribute [local irreducible] HasDerivedCategory.standard

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme
open scoped Obj

namespace WeilConjectures.LocallyFiniteAdicRealization
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)

attribute [local irreducible] sections CoefficientPresentation.integralMap
  completedTensorComparison

variable (l : ℕ) [Fact l.Prime] (X : Scheme.{u})

/-- Finite-field continuous coefficient presentations, compatible with field inclusion.

Source: Bhatt--Scholze, Lemma 6.8.2; native realization proof step 2
(blueprint: lem-sf-locally-finite-adic-coefficient-presentations).

Proof in words: for each positive residue quotient, the constant-sheaf comparison to
continuous functions is an isomorphism: locally a discrete-valued function is constant,
and constants are locally injective. Use these comparisons as the finite components.
Both the completed integral ring sheaf and the sheaf of continuous integral functions
are limits of this same residue tower. The unique comparison of limiting cones gives
the integral isomorphism and its residue normalization. Localizing the integral function
sheaf at a uniformizer gives the rational function sheaf: each continuous rational
function is locally bounded, so locally some uniformizer power makes it integral.
The integral inclusion and localization comparison have the specified pointwise values.
Postcomposition by the displayed finite-field embedding gives rational inclusion into
the native ring: its range lies in a finite-dimensional subspace, hence is locally finite.
These maps are natural on site objects. Their pointwise definitions preserve zero, one,
addition and multiplication. For a finite-field extension, evaluation of the completed
scalar map followed by native inclusion is the original embedded rational function.
For each target residue precision, use continuity of integral field inclusion to
choose a source precision whose ideal maps into the target ideal. Compare at that
precision using the defining completed scalar map and the integral comparison. The
comparison is unchanged on deepening the source precision, including ramified field
extensions. Joint injectivity of the target projections identifies the integral section.
Composition of the two field embeddings is the original embedding,
which proves the scalar equation. All pointwise and limiting arguments include the
empty site object and repeated fields without any nonemptiness assumption.
-/
theorem coefficientPresentations_exists
    (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) [IsCommMonObj (abRing l X)] :
    ∃ coefficient : ∀ E : Index l (PadicAlgCl l),
      CoefficientPresentation l X (Coefficient.{u} l (PadicAlgCl l) E) (embedding l E),
      ∀ (E L : Index l (PadicAlgCl l)) (h : E ≤ L),
        completedCoefficientMap l (Coefficient.{u} l (PadicAlgCl l) E)
            (Coefficient.{u} l (PadicAlgCl l) L)
            (coefficientInclusion l (PadicAlgCl l) E L h) X ≫
          (coefficient L).integralMap l X = (coefficient E).integralMap l X := by sorry

end WeilConjectures.LocallyFiniteAdicRealization
