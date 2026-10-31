/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
public import WeilConjectures.AlgebraicGeometry.NormalScheme
public import WeilConjectures.Topology.PresheafModuleStalkFunctor
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.AlgebraicGeometry.ResidueField
import WeilConjectures.AlgebraicGeometry.Dimension
import WeilConjectures.AlgebraicGeometry.Regular

/-!
# Local principal ideal domains of a normal curve

Source: Stacks Project, Tag 0CCK, proof of the flatness lemma; Tag 0B8Y,
regular points on curves; Tag 00PD, characterization of discrete valuation rings.
(blueprint: lem-a1-normal-curve-local-principal-domains)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The local rings of a normal integral curve are Noetherian domains of dimension at most
one: they are fields in dimension zero and discrete valuation rings in dimension one,
and therefore principal ideal domains.

Source: Stacks Project, Tag 0CCK, first sentence of the proof; Tag 0B8Y; Tag 00PD.
(blueprint: lem-a1-normal-curve-local-principal-domains)

Proof:
1. Every ideal of the field `k` is zero or the unit ideal, so `k` is Noetherian. Thus
   `Spec k` is locally Noetherian. The finite-type structure morphism of the curve is
   locally of finite type, so the curve is locally Noetherian (Tag 01T6).
2. Choose a Noetherian affine neighbourhood of `y`. Its germ map is localization at the
   prime corresponding to `y` (Tag 01HV). Localization preserves Noetherianity (Tag 00FN),
   giving Noetherianity of the stalk.
3. Normality gives an integrally closed domain, and a scheme stalk is local. The curve
   has dimension one, equal to the supremum of its stalk dimensions. Hence the stalk
   dimension is at most one. The zero prime gives dimension at least zero, so its
   dimension is zero or one.
4. In dimension zero the maximal ideal must be zero: otherwise the zero prime and the
   maximal ideal form a strict chain of length one. The stalk is then isomorphic to its
   residue field and is a field.
5. In dimension one the stalk is a Noetherian normal local domain of dimension one, so
   Tag 00PD, condition (5) implies (1), makes it a discrete valuation ring. No perfection
   or residue-field separability is required.
6. Every ideal in a field is zero or the unit ideal. Every ideal in a discrete valuation
   ring is principal by definition. The stalk is a domain in both cases, hence a PID. -/
theorem IsIntegralCurve.stalk_local_principal_domains {k : Type u} [Field k]
    {Y : Scheme.{u}} (f : Y ⟶ Spec (.of k)) [IsIntegralCurve f]
    (hY : IsNormalScheme Y) (y : Y) :
    IsNoetherianRing (Y.presheaf.stalk y) ∧
      ringKrullDim (Y.presheaf.stalk y) ≤ 1 ∧
      (ringKrullDim (Y.presheaf.stalk y) = 0 → IsField (Y.presheaf.stalk y)) ∧
      (ringKrullDim (Y.presheaf.stalk y) = 1 →
        IsDiscreteValuationRing (Y.presheaf.stalk y)) ∧
      (ringKrullDim (Y.presheaf.stalk y) = 0 ∨ ringKrullDim (Y.presheaf.stalk y) = 1) ∧
      IsDomain (Y.presheaf.stalk y) ∧ IsPrincipalIdealRing (Y.presheaf.stalk y) := by
  sorry

end AlgebraicGeometry
