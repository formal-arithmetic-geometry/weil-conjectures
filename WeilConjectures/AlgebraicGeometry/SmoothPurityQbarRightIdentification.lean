/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityQbarFinitePackage

/-! # Identifying the finite-stage smooth-purity right functor

The finite package has an abstract descended right stage morphism.  This module
records the separate comparison with the intrinsic pullback, Tate twist, and shift.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)

/-- The abstract right stage morphism is isomorphic to the intrinsic purity functor.
Source: `sk-thm-sp-qbar`, coefficient extension and finite descent paragraphs;
`det-sp-field-extension-towers`, `det-sp-qbar-finite-descent`, and
`det-sp-unique-right-adjoint`, and `prop-pur-condensed-rational-adjunction`
(blueprint: d4-sp-qbar-right-identification).

Proof: at each finite coefficient field use the integral purity isomorphism and
the native condensed rational adjunction of prop-pur-condensed-rational-adjunction
to identify the normalized compact-support right adjoint with
pullback, signed Tate tensor, and [2d]. Compare it with P.stageAdjunction at that
field using right-adjoint uniqueness and P.action.finite_eq. The comparison is the
unique counit-compatible one. The field-extension counit equations and
the counit_compatible equation of P show that these comparisons agree under every
coefficient extension: transposing either route gives the same normalized counit.
They therefore descend to the common-stage pair categories. On a pair represented
at E, use that finite comparison; to check naturality, represent an arrow at one
common overfield and use finite naturality there. Eventual equality of representatives
makes this independent of choices. Apply the same construction to inverse components;
the two composites are identities at every finite stage and hence on common-stage
objects. Finally the canonical coefficient comparisons for pullback, Tate tensor, and
shift identify the descended explicit functor with qbarPurityRightFunctor. Compose
this identification with the descended comparison to obtain the asserted natural
isomorphism. No literal equality of arbitrary right functors is asserted.
-/
theorem smoothPurityQbarFinitePackage_right_identification
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y : Scheme.{u}} [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [IsSeparated (Y ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D.k))]
    [QuasiCompact (Y ↘ Spec (.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) [SmoothOfRelativeDimension d f] (c : Compactification f)
    (P : SmoothPurityQbarFinitePackage D l hl Ω f c) :
    Nonempty (P.right.functor ≅ qbarPurityRightFunctor D l hl Ω f d) := by
  sorry

end WeilConjectures
