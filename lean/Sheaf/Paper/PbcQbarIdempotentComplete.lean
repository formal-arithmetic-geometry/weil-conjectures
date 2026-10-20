/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.Paper.PbcQbarCategory
public import WeilConjectures.CategoryTheory.Idempotents.Triangulated

import Sheaf.Paper.PbcFilteredRetractDescent
import Sheaf.Paper.PbcFiniteStageKaroubian

/-! # Idempotent completeness of the Qbar coefficient category

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc`, order 1542
(blueprint: thm-weil-pbc-qbar-idempotent-complete).

The category is the existing raw finite-stage pair category, with its common-stage
triangulation. The envelope uses the canonical shift and retract triangulation.
-/

@[expose] public section

set_option autoImplicit false

universe w u

open CategoryTheory CategoryTheory.Idempotents

namespace AlgebraicGeometry.Scheme

/-- The raw Qbar coefficient category is idempotent complete, and its canonical fully
faithful inclusion into its Karoubi envelope is an exact equivalence.

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc`, order 1542
(blueprint: thm-weil-pbc-qbar-idempotent-complete).

Proof:
1. For every finite coefficient field E, thm-weil-pbc-finite-stage-karoubian gives
   idempotent completeness of the actual raw rational stage. Apply
   prop-weil-filtered-retract-descent to these stages: an idempotent representative
   becomes genuinely idempotent after passage to one finite overfield, where it splits.
   Its splitting descends to the pair category. Thus every idempotent splits there.
2. The canonical functor J sends X to (X, identity) and acts identically on arrows.
   lem-weil-karoubi-envelope-fully-faithful gives its full faithfulness.
3. Given (X,e) in the envelope, choose a splitting i : S -> X, p : X -> S with
   i followed by p equal to identity and p followed by i equal to e. The splitting
   equations make i and p envelope morphisms and exhibit J(S) isomorphic to (X,e).
4. Choose such splittings and send an envelope arrow u : (X,e) -> (Y,d) to
   i_X followed by u followed by p_Y. The splitting and envelope morphism equations
   give the functor laws, the unit and counit isomorphisms and the triangle identities.
   Bilinearity makes this quasi-inverse additive. Hence J is an equivalence.
5. thm-weil-pbc-verdier-axioms supplies the specified common-stage triangulation.
   lem-weil-karoubi-envelope-triangulated gives the canonical shifted retract
   triangulation on the envelope and exactness of J for its canonical shift comparison.
   Together with step 4 this is the asserted exact equivalence. -/
theorem pbcQbarIdempotentComplete
    (l : ℕ) [Fact l.Prime] (Qbar : Type w)
    [Field Qbar] [Algebra (Padic l) Qbar] [IsAlgClosure (Padic l) Qbar]
    (T : Scheme.{u}) [IsNoetherian T]
    [hDim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞))]
    [hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))] :
    IsIdempotentComplete (pbcQbarCategory l Qbar T) ∧
      (toKaroubi (pbcQbarCategory l Qbar T)).Full ∧
      (toKaroubi (pbcQbarCategory l Qbar T)).Faithful ∧
      (toKaroubi (pbcQbarCategory l Qbar T)).IsEquivalence ∧
      (toKaroubi (pbcQbarCategory l Qbar T)).IsTriangulated := by
  have hC : ∀ E : Padic.FiniteCoefficientFields l Qbar,
      IsIdempotentComplete (pbcStageCategory l Qbar T E) := by
    intro E
    exact (finite_stage_karoubian l (pbcFiniteField.{u} l Qbar E) T).1
  have : IsIdempotentComplete (pbcQbarCategory l Qbar T) :=
    (pbcFilteredRetractDescent l Qbar T hDim.out hInv.out hC).1
  exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme
