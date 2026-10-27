/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.Paper.FiniteClopenExceptionalRestriction


/-! # Transport of the common-stage part of a clopen exceptional comparison

Source: blueprint section-invariant, finite-clopen exceptional restriction, Step 3.
(blueprint: lem-pur-clopen-exceptional-action-transport).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

variable (P : PurityFiniteSetting.{u})
    (X Y : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType (X.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (X.left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y.left ↘ Spec (.of P.field.k))]
    (g : X.left ⟶ Y.left) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]

/-- The common-stage part of an existing clopen comparison can use the fixed
identity comparison's global action. Its independent base-field record is retained.
This statement concerns only the algebraically closed coefficient stages: it neither
constructs an initial comparison nor synchronizes the base integral/rational functors.

Source: the simultaneous-choice argument of finite-clopen inverse assembly, Step 3;
clopen exceptional scalar descent, coefficient-extension and common-stage clauses.
(blueprint: lem-pur-clopen-exceptional-action-transport).

Proof: at each finite coefficient stage retain the global strict system of R and
restrict it to the clopen component. The clopen counit comparison supplies the
component adjoint and its normalized strict square. Transport its site comparison,
finite evaluations and actual inverse-limit realization as one diagram, using the
unique counit-preserving right-adjoint isomorphisms to identify any presentations
of the component. Extend the integral maps on pure tensors. Choose the rational
adjunctions with the global adjunction of R; transport the component adjunctions
through the same restriction comparisons. For coefficient extension use the mates
of the fixed global compact-support scalar comparisons of R, and the component
compact-support scalar comparisons. The sectionwise open-extension square commutes
with scalar extension; mate pasting therefore gives the commuting restriction
square, including identity and successive extensions and the ramified cofinal
reindexing. These commuting squares descend the stagewise restriction maps and
their inverses to the common-stage comparison, with its prescribed representative
formula. Thus the stage records, component action, adjunctions and comparisons
satisfy all all-coefficients coherence fields with global action R.action.
Finally use S.base for the independent base record: the all-coefficients coherence
predicate mentions only stages, actions, scalar mates and common-stage maps, so
this replacement changes no coherence equation. The identity inclusion is just
counit-preserving adjoint transport. For an empty component every component map
is the unique zero map; no nonempty component or partition is required. -/
theorem clopenExceptional_action_transport
    (Xi : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType (Xi.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Xi.left ↘ Spec (.of P.field.k))]
    (c : Compactification g) (j : Xi ⟶ X)
    [IsOpenImmersion j.left] [IsClosedImmersion j.left]
    (R : ClopenExceptionalAllCoefficients P X Y X g c (𝟙 X))
    (S : ClopenExceptionalAllCoefficients P X Y Xi g c j) :
    ∃ T : ClopenExceptionalAllCoefficients P X Y Xi g c j,
      T.base = S.base ∧ T.action.functor = R.action.functor := by sorry

end WeilConjectures.PurityFiniteSetting
