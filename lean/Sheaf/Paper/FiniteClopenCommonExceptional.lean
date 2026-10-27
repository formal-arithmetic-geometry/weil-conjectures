/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P4
-/
module

public import Sheaf.Paper.FiniteClopenExceptionalRestriction

/-! # One exceptional system for all members of a finite clopen partition

Source: blueprint section-invariant, finite-clopen exceptional restriction, Step 3.
(blueprint: lem-pur-finite-clopen-common-exceptional).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u w
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

variable (P : PurityFiniteSetting.{u})
    (X Y : Over (Spec (.of P.field.k)))
    [LocallyOfFiniteType (X.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (X.left ↘ Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y.left ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y.left ↘ Spec (.of P.field.k))]
    (g : X.left ⟶ Y.left) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]

/-- The component comparisons can share one global exceptional system. This asserts
neither smoothness nor invertibility and includes the empty partition.

Source: blueprint section-invariant, Step 3 of the finite-clopen inverse assembly;
finite-clopen exceptional restriction, construction of the strict adjoint square.
(blueprint: lem-pur-finite-clopen-common-exceptional).

Proof: first fix the compactification c and its global strict compact-support system.
Choose its exceptional right adjoint once, with its finite evaluation comparisons.
For each clopen inclusion, form the component compactification by precomposition.
Extension by zero identifies the sum of component supports with the global support.
Transpose the coordinate-insertion maps through these adjunctions. The resulting
strict restriction squares use the same global system and adjoint for every i.
Apply the normalized site realization and the same restriction-of-scalars/derived
limit to that global system, once. Use these functors as the global fields of every
component comparison. The identity inclusion gives R. Rationalize these same
functors and extend their maps linearly. At every finite coefficient field make
the same common choice, and use the counit mates of the fixed support scalar action
for the coefficient transitions. Their identity and composition equations follow
from mate pasting. Thus the resulting common-stage action is shared as well.
The component square, its evaluations and its limit map satisfy the coherence
fields by the same transposition and limit formulas as finite-clopen exceptional
restriction. The three equalities are reflexive for these simultaneous choices.
For an empty family only the identity comparison is required, and the construction
of the global exceptional system still applies. No arbitrary levelwise maps are
lifted, and no tensor inverse or relative-dimension assertion is used. -/
theorem finiteClopen_common_exceptional
    {I : Type w} [Finite I]
    (Xi : I → Over (Spec (.of P.field.k)))
    [∀ i, LocallyOfFiniteType ((Xi i).left ↘ Spec (.of P.field.k))]
    [∀ i, QuasiCompact ((Xi i).left ↘ Spec (.of P.field.k))]
    (j : ∀ i, Xi i ⟶ X)
    [∀ i, IsOpenImmersion (j i).left] [∀ i, IsClosedImmersion (j i).left]
    (hdisjoint : ∀ i k, i ≠ k → Disjoint (Set.range (j i).left) (Set.range (j k).left))
    (hcover : (⋃ i, Set.range (j i).left) = Set.univ)
    (c : Compactification g) :
    ∃ R : ClopenExceptionalAllCoefficients P X Y X g c (𝟙 X),
      ∃ Ri : ∀ i, ClopenExceptionalAllCoefficients P X Y (Xi i) g c (j i),
        ∀ i, (Ri i).base.integral = R.base.integral ∧
          (Ri i).base.rational = R.base.rational ∧
          (Ri i).action.functor = R.action.functor := by sorry

end WeilConjectures.PurityFiniteSetting
