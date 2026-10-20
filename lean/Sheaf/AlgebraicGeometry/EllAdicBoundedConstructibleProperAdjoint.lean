/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperShriek
public import Sheaf.AlgebraicGeometry.EllAdicCondensedCoefficient

/-! # A coefficient-generic interface for proper bounded constructible adjunctions

Source: the three proper-adjoint inputs of the bounded constructible upper shriek.
(blueprint: lem-sfb-adic-bounded-constructible-proper-adjoint)
-/

@[expose] public section

universe u

open CategoryTheory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

variable {Z Y : Over (Spec (.of k))}
  [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (g : Z ⟶ Y)

/-- The proper bounded constructible pushforward has a right adjoint for a certified
ell-adic coefficient ring.

Source: blueprint `sk-def-sfb-dc-upper-shriek`, the three proper-adjoint coefficient cases.
(blueprint: lem-sfb-adic-bounded-constructible-proper-adjoint)

Proof: eliminate the coefficient certificate. Its continuous constructor specifies a
finite normed extension of the ell-adic field, its integral constructor specifies a finite
subextension of the algebraic closure with its ring of integers, and its algebraic-closure
constructor specifies that closure itself. Each case is precisely the corresponding
upstream proper-pushforward instance. The certificate indexes the monoid-object structure,
so the functor in each case has the canonical coefficient multiplication required there.
This theorem uses those inputs; it does not claim to prove their remaining geometric holes.
-/
theorem ellAdic_isLeftAdjoint_boundedConstructibleLowerStar [IsProper g.left]
    [IsFinitenessCoefficient ℓ Λ]
    (hΛ : IsEllAdicCoefficient ℓ Λ inferInstance) :
    (boundedConstructibleLowerStar Λ ℓ g).IsLeftAdjoint := by
  cases hΛ with
  | continuous E =>
    exact isLeftAdjoint_boundedConstructibleLowerStar_continuousMapRingObj ℓ g E
  | integral E =>
    exact isLeftAdjoint_boundedConstructibleLowerStar_padicIntegersRingObj ℓ g E
  | algebraicClosure =>
    exact isLeftAdjoint_boundedConstructibleLowerStar_padicAlgClRingObj ℓ g

end AlgebraicGeometry.ProEtale.CondensedRing
