/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q92
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Irreducible
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Sheaf.AlgebraicGeometry.Morphisms.GenericAlgebraicityQuasiFiniteDimensionOne
import WeilConjectures.AlgebraicGeometry.QuasiFiniteAtPointIsolated

/-!
# Finite discrete fibre over a DVR point

Source: Stacks Project, Varieties, Tags 0BFP and 0AB7, using Tag 0AB6;
Algebra, Tag 00PD (blueprint: lem-sfb-proper-generically-algebraic-dvr-fibre).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A proper morphism with algebraic residue extensions at component generic points has
finite discrete fibre over a point with a dimension-one DVR stalk. That stalk is Noetherian
and normal, and the morphism is quasi-finite at every point above the given point.

Source: Stacks Project, Varieties, Tag 0BFP, proof (2), and Tag 0AB7, proof through the
finite discrete fibre; Tag 0AB6, condition (1), and Algebra, Tag 00PD
(blueprint: lem-sfb-proper-generically-algebraic-dvr-fibre).

The domain instance is part of the DVR hypothesis. Normality is expressed by normality of
all prime localizations, as in def-weil-pbc-normal-ring. The fibre identification is a
homeomorphism whose composite with the subtype inclusion is the first projection.

Proof:
1. The DVR stalk is a principal ideal domain by def-sc-discrete-valuation-ring. Apply
lem-weil-pbc-pid-noetherian-normal to obtain Noetherianness and integral closedness, hence
normality of this local domain.
2. Properness gives finite type and hence local finite type (def-weil-proper-morphism,
def-weil-finite-type-morphism). Apply
lem-sfb-generically-finite-quasifinite-over-dimension-one: Step 1 gives its Noetherian
hypothesis, the assumed dimension equals one, and its generic residue algebraicity is
exactly the hypothesis here. Every point above x is therefore quasi-finite.
3. By def-pc-scheme-fibre, fiberHomeo identifies the scheme fibre with the subspace
f inverse-image of {x}, through the first projection. By Step 2 and
lem-weil-pbc-quasi-finite-at-point-isolated each singleton in the fibre is open. Every
subset is a union of these singletons, so the fibre has the discrete topology.
4. By lem-weil-pbc-proper-fp-permanence (b), the projection of the fibre to Spec of the
residue field is proper. By def-weil-proper-morphism and def-weil-finite-type-morphism
it is quasi-compact. The base is affine (def-weil-affine-spectrum), so the whole fibre
is quasi-compact.
5. The cover of the fibre by its open singletons has a finite subcover by Step 4.
Consequently its underlying set is finite, also when the fibre is empty. Combine this
with Steps 1--3 to obtain every conclusion.
-/
theorem proper_generic_algebraicity_dvr_fibre
    {Y X : Scheme.{u}} (f : Y ⟶ X) [IsProper f] (x : X)
    [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (hdim : ringKrullDim (X.presheaf.stalk x) = 1)
    (hgeneric : ∀ (T : Set Y), T ∈ irreducibleComponents Y →
      ∀ (η : Y), IsGenericPoint η T →
        @Algebra.IsAlgebraic (X.residueField (f η)) (Y.residueField η) _ _
          (f.residueFieldMap η).hom.toAlgebra) :
    IsNoetherianRing (X.presheaf.stalk x) ∧
      (∀ (p : Ideal (X.presheaf.stalk x)) [p.IsPrime],
        IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) ∧
      (∀ y : Y, f y = x → Scheme.Hom.IsQuasiFiniteAtPoint f y) ∧
      Finite (f.fiber x) ∧ DiscreteTopology (f.fiber x) ∧
      ∃ e : f.fiber x ≃ₜ (f ⁻¹' {x}), ∀ z : f.fiber x, (e z).val = f.fiberι x z := by
  sorry

end AlgebraicGeometry
