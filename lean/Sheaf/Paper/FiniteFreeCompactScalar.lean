/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K8
-/
module

public import Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions

/-! Scalar compatibility for the specified finite-coefficient operations. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
open WeilConjectures.FiniteFreeCoefficients
namespace WeilConjectures.FiniteFreeProjectionExchange

/-- The finite-free scalar comparison for compact support is an isomorphism and commutes
with the published coherent compactification identifications on bounded-below origins.
Source: Stacks 0GL6; blueprint main-20261015, sk-thm-purity-transport,
proof Steps 1 and 3 (blueprint: lem-pur-finite-free-compact-scalar).

Proof: choose a finite basis of B over A only to check invertibility. Scalar extension
then becomes a finite direct sum; exact derived direct image commutes with this finite
sum. The counit equation identifies its comparison with Sites.direct. ScalarOpen is
an isomorphism by adjoint uniqueness, so their displayed composite is an isomorphism
on every object. Its naturality follows from direct-image and scalarOpen naturality.
For an etale proper refinement apply the proper/open coefficient refinement square
and the direct-image composition identity. The cocycle of the canonical etale
compactification comparison extends this to arbitrary pairs of compactifications.
For the pro-etale realization conjugate this square by the site comparison, using
the open unit normalization and the proper counit normalization. The canonical
proper/open site normalization identifies the conjugated arrow with refinement.
Naturality of refinement in its input yields the equation for every isomorphic
scalar representative e. The finite-free extension preserves bounded-below objects,
so all these canonical bounded-below comparisons apply. -/
theorem finite_free_compact_scalar {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B)
    (_hφ : letI := φ.toAlgebra; Module.Finite A B ∧ Module.Free A B) :
    ∀ (pro : Bool) {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f],
      (∀ (c : Compactification f) (M : Sites.D pro A X),
        IsIso (comparison pro φ c M)) ∧
      (∀ (c d : Compactification f)
        (M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
        (N : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)))
        (e : (origin pro B X).obj N ≅
          (Sites.scalar pro φ X).obj ((origin pro A X).obj M)),
        RefinementEquation pro φ c d M N e) := by
  sorry

end WeilConjectures.FiniteFreeProjectionExchange
