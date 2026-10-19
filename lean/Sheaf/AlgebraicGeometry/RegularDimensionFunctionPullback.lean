/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Sheaf.AlgebraicGeometry.GeometricDimensionFunction
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.KrullDimension.Basic
import Sheaf.AlgebraicGeometry.FibreStalkQuotient
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Sheaf.AlgebraicGeometry.DimensionFunctionsStrictLocalization
import Sheaf.AlgebraicGeometry.LocalDimensionFunctionCalculus
import Sheaf.AlgebraicGeometry.RegularStrictLocalModel
import Sheaf.AlgebraicGeometry.StrictLocalRegularIntegralFibres

/-!
# Regular pullback of dimension functions

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XIV, Proposition 2.5.4,
printed pp. 217--218 (blueprint: lem-per-regular-dimension-function-pullback).

The natural-valued function in the conclusion is identified with the actual local-ring
Krull dimension before its integer coercion is subtracted. This records finiteness and
does not truncate an extended dimension or assume a finite-type morphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A regular morphism of Noetherian excellent schemes pulls a dimension function back
by subtracting the local dimension of the fibre.
Source: ILO XIV, Proposition 2.5.4, pp. 217--218
(blueprint: lem-per-regular-dimension-function-pullback).

Proof:
1. By lem-per-dimension-functions-strict-localization it suffices to work on each
   strict localization of P. The node lem-per-regular-strict-local-model gives a local
   regular map Y = Spec B to S = Spec A of Noetherian excellent strictly local schemes,
   preserving all fibre local dimensions. Flatness is stalkwise, hence A to B is flat.
2. Choose a dimension function d on Y by lem-per-local-dimension-function-calculus.
   Excellence and lem-per-immediate-specialization-criterion imply that d(v) - d(w)
   is the dimension of the reduced local closure for every specialization v to w:
   sum the unit drops along a saturated chain. The same holds for the base function.
3. For each prime p of A, lem-per-strict-local-regular-integral-fibres makes the
   geometric fibre integral. The ordinary fibre ring F_p injects into its extension
   to an algebraic closure: a linear functional sending 1 to 1 supplies a retraction.
   Thus F_p is a domain.
4. By lem-weil-pbc-flat-module-base-change, C_p = B/pB is flat over A/p.
   By lem-trf-flat-module-torsionfree-domain its map to its localization F_p is
   injective. Therefore C_p is a domain and q_p = pB is prime, contracts to p, and
   is the unique generic point of the fibre. Apply this also at the maximal ideal m.
5. Apply lem-weil-pbc-flat-height-formula to A/p to C_p at q_m/pB.
   The closed local fibre is the fraction field of B/mB, of dimension zero, so
   dim (C_p)_(q_m/pB) = dim A/p. No finite-type hypothesis is used.
6. The chain formula in Step 2 and Step 5 give
   delta_S(p) - d(q_p) = delta_S(m) - d(q_m).
7. For q over p, lem-sbc-scheme-fibre-stalk-quotient identifies the reduced local
   closure from q_p with B_q/pB_q, the fibre local ring at q. Step 2 gives
   d(q) = d(q_p) - b(q). These local Noetherian rings have finite natural dimensions.
8. Hence delta_S(p) - b(q) = d(q) + delta_S(m) - d(q_m), a dimension function.
   Descend by lem-per-dimension-functions-strict-localization. Empty sources impose
   no conditions; zero-dimensional fibres and length-zero chains are included.
-/
theorem regular_pullback_isGeometricDimensionFunction
    {P X : Scheme.{u}} (r : P ⟶ X) [IsNoetherian P] [IsNoetherian X]
    (hP : ∀ U : P.affineOpens, IsExcellent Γ(P, U))
    (hX : ∀ U : X.affineOpens, IsExcellent Γ(X, U)) [Flat r]
    (hregular : ∀ (x : X) (L : Type u) [Field L]
      [Algebra (X.residueField x) L] [Module.Finite (X.residueField x) L],
      IsRegularScheme (pullback (r.fiberToSpecResidueField x)
        (Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) L)))))
    (δX : X → ℤ) (hδX : IsGeometricDimensionFunction X δX) :
    ∃ b : P → ℕ,
      (∀ p : P, ringKrullDim ((r.fiber (r p)).presheaf.stalk (r.asFiber p)) =
        (b p : WithBot ℕ∞)) ∧
      IsGeometricDimensionFunction P (fun p ↦ δX (r p) - (b p : ℤ)) := by
  sorry

end AlgebraicGeometry.Scheme
