/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import
  WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory


/-! # Proper pushforward has a right adjoint for condensed algebraic-closure coefficients

Source: latest blueprint, `part-six-operations/sec-coefficients-constructible/sec-n-brown/`
`sk-thm-existence/lem-sfb-dc-proper-pushforward-left-adjoint-qlbar.md`, statement and
its adjacent proof
(blueprint: lem-sfb-dc-proper-pushforward-left-adjoint-qlbar).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Scheme

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Over a finite or algebraically closed base field, proper direct image on bounded
constructible complexes with the finite-subextension-valued
condensed algebraic-closure coefficient ring has a right adjoint.

Source: latest blueprint, `part-six-operations/sec-coefficients-constructible/sec-n-brown/`
`sk-thm-existence/lem-sfb-dc-proper-pushforward-left-adjoint-qlbar.md`, statement and
its adjacent proof
(blueprint: lem-sfb-dc-proper-pushforward-left-adjoint-qlbar).

Proof:
1. Index finite coefficient fields by their directed poset. Scalar extension preserves bounded
constructibility; tensor associativity supplies coherent transitions and cocones. At each
finite field choose the proper direct-image adjunction. Object descent and Hom descent in the
algebraic-closure two-colimit, with degree zero for Hom, give object representatives, morphism
representatives and eventual equality.
2. The finite direct-image scalar comparisons are invertible and obey the identity and tower
laws. Their counit transposes between the finite right adjoints are invertible, coherent and
compatible with the Hom bijections, units and counits. These give a compatible system of
finite adjunctions, before choosing any algebraic-closure right adjoint.
3. Use the actual restricted algebraic-closure pushforward as the limiting left functor.
Properness and boundedness make its canonical scalar comparisons invertible; the coefficient
composition equation makes these compatible with finite enlargement and cocone associators.
4. Finite-stage adjunction descent now assembles a functor and natural Hom bijections for this
actual left functor. On an object descended from a finite field its right adjoint is the
scalar extension of the finite-field right adjoint, so remains bounded constructible. The
assembly supplies functoriality, independence of the representative and the counit. This is
`Rp^!`. No additional cohomological-dimension hypothesis is imposed in this standing domain.
-/
theorem properPushforwardLeftAdjointQlbar
    (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
    (hk : Finite k ∨ IsAlgClosed k)
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
    {Z Y : Over (Spec (.of k))}
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (p : Z ⟶ Y) [IsProper p.left] :
    (boundedConstructibleLowerStar ℓ p).IsLeftAdjoint := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
