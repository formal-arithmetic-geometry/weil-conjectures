/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C3
-/
module

public import Sheaf.SixFunctors.TensorExchangePresentation

/-! # Normalized adjunction ingredients

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-package/
fix-lem-tensor-adjunction.proof.md (blueprint: lem-sf-tensor-exchange-normalized-models).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.TensorAdjunctionExchange
open ConstructibleExceptionalCoefficients

/-- The normalized inputs of the five-arrow exchange argument exist.
Source: Step 1, the tensor-Hom bijections and the inverse projection arrow
(blueprint: lem-sf-tensor-exchange-normalized-models).

Proof: restrict the specified ordinary pullback/direct-image adjunction to the
full finite-Tor domains, using the finite and uniform integral bounds of
lem-sf-tensor-exchange-ctf-domains and cor-sf-direct-image-ctf-proetale. Restrict
internal Hom and its evaluation using the same bounds. Tensor-Hom is the ringed
closed adjunction; integrally compose with the completion-unit mapping property
of lem-sf-ambient-completed-tensor-adjunction, since its targets are complete.
Restrict the projection isomorphism of fix-prop-projection-formula, reversing it
and applying the two published signed braidings to obtain the convention of
Model.projection. Retain its proper-counit/open-projection normalization.
Localize these ingredients over every finite coefficient field, and pass to
common finite stages for the algebraic closure. These constructions give the
six partial realizations and the ringed realizations. The supplied datum gives
its operations at E; at every other field use the same completed/localized
constructions. Transport the chosen System adjunctions by uniqueness of right
adjoints, retaining both transpose equations. The projection normalization is
preserved by this transport, giving precisely NormalizedDatum, including its
rational and common-stage equations. No exchange isomorphism or shift conclusion
is asserted by this construction. Empty schemes use zero functors, and all
finite levels are positive by their existing PNat indices. -/
theorem normalized_models
    (D : FiniteFieldDatum.{u}) (A : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic A.l) E]
    [FiniteDimensional (Padic A.l) E] (n : ℕ) (hn : 1 ≤ n)
    (six : SixFunctorOperationDatum D A E n hn)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (S : System A.l A.Qbar D A.different (f := f.hom.left))
    (c : Compactification f.hom.left) :
    ∃ core : Presentation A.l A.Qbar D A.different f.hom.left S c,
      NormalizedDatum D A E n hn six f S c core := by
  sorry

end WeilConjectures.TensorAdjunctionExchange
