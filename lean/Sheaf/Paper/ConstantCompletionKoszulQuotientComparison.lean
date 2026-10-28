/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.Paper.ConstantCompletionCore

/-! # Comparison of strict Koszul and quotient completion

Source: Stacks Project, proetale.tex, Tag 099M (lemma-naive-completion).
(blueprint: lem-weil-pbc-constant-koszul-quotient-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory

namespace CategoryTheory.ConstantCompletion

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
variable (A : Type u) [CommRing A] (I : Ideal A)

/-- For any presentation of the specified strict Koszul tower, its derived limit agrees
with quotient completion, carrying the degree-zero unit to the quotient augmentation.

Source: Stacks Project, proetale.tex, Tag 099M (lemma-naive-completion), with the
flat completed-coefficient extension of sites-modules.tex, Tag 093M.
(blueprint: lem-weil-pbc-constant-koszul-quotient-comparison).

Proof: use the exterior basis to identify the dual of the positive tensor Koszul complex
with the negative Koszul complex on the same ordered generators. The diagonal power
transition is multiplication by a_i on the negative-degree factor and identity in degree
zero. The degree-zero augmentation therefore commutes strictly with the transitions and
with the coaugmentation from the ring. The Noetherian Koszul augmentation theorem says
that its cone tower is pro-zero, including the empty generating list. Apply exact constant
module realization, followed by extension to the chosen coefficient sheaf. This extension
is flat: it is the identity for constant coefficients, and is flat by Tag 093M for completed
coefficients. Its quotient is the specified finite coefficient sheaf. Tensor with a
flat-term K-flat representative P. The flat-constant tensor pro-zero theorem and the total
right derived strict-limit theorem invert the resulting augmented tower map. The quotient
presentation comparison computes the quotient tower on P; the Koszul presentation
factorization computes its strict tensor tower. Uniqueness of the total derived limit
identifies the two limit functors, independently of the supplied Koszul presentation.
The construction commutes with maps between K-flat representatives. Resolving-class
localization therefore descends these comparisons to a natural isomorphism on the derived
category. The strict coaugmentation square and the defining normalization of the quotient
presentation give the displayed equality of units on K-flat models, and essential
surjectivity of their localization gives it on every derived object. -/
theorem koszulQuotientComparison [IsNoetherianRing A] (b : Bool) (r : ℕ)
    (a : Fin r → A) (ha : Ideal.span (Set.range a) = I)
    (K : KoszulPresentation J A I b r a) :
    ∃ e : koszulCompletion J A I K ≅ completion J A I b,
      ∀ M : D (coefficients J A I b), koszulUnit J A I K M ≫ e.hom.app M =
        (completionUnit J A I b).app M := by sorry

end CategoryTheory.ConstantCompletion
