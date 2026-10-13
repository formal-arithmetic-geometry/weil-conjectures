/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.RingTheory.FormallySmoothAdic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Noetherian.Defs

/-! # Extending a parameter-vanishing defect derivation

Source: Stacks Project, Tags 07NQ and 07EL, the differential extension argument.
(blueprint: lem-weil-pbc-closed-fiber-defect-derivation-extension)
-/

@[expose] public section

universe u v w

open IsLocalRing

namespace Algebra

/-- The defect of a ring lift agreeing on generators of the base maximal ideal extends
to a derivation on the target. The displayed additive map is a Z-derivation with
values in J, using the T-action induced by f.
Source: Stacks Project, Tag 07NQ, differential factorization and extension before psi'.
(blueprint: lem-weil-pbc-closed-fiber-defect-derivation-extension)

Proof: Give J its T-module structure through f; square-zero makes this independent
of the representative of g. The annihilation hypothesis makes J a vector space over
K = T/m_T, and the local map makes its R-action factor through k = R/m_R.
The difference f composed with R -> T minus R -> D is additive, satisfies Leibniz,
and has values in J. It vanishes on t. Its differential functional therefore kills
the conormal image for m_R: the differentials of the generators t span this image,
and m_R acts trivially on J. The quotient differential exact sequence factors the
functional through Omega_(k/Z). Extend scalars to K. Adic formal smoothness of the
closed fibre gives injectivity of its base-field differential map after tensoring
with K (Tag 07EL). Extend the functional along this injection using a vector-space
basis, and precompose with the differential of T -> T/L. This gives the required
derivation delta on T, with the prescribed restriction. Its values lie in J,
Leibniz uses the f-action, and every derivation kills 1. For J = 0 use the zero map;
for t empty the base maximal ideal is zero and the same factorization applies.
-/
theorem exists_closedFiber_defect_derivation
    (R : Type u) (T : Type v) [CommRing R] [CommRing T]
    [IsLocalRing R] [IsLocalRing T] [IsNoetherianRing T]
    [Algebra R T] [IsLocalHom (algebraMap R T)]
    (t : List R) (ht : Ideal.span {r | r ∈ t} = maximalIdeal R) :
    let L : Ideal T := (maximalIdeal R).map (algebraMap R T)
    letI : Algebra (R ⧸ maximalIdeal R) (T ⧸ L) :=
      Ideal.Quotient.algebraQuotientOfLEComap (Ideal.le_comap_map :
        maximalIdeal R ≤ L.comap (algebraMap R T))
    FormallySmoothAdic (R ⧸ maximalIdeal R) (T ⧸ L)
        ((maximalIdeal T).map (Ideal.Quotient.mk L)) →
    ∀ (D : Type w) [CommRing D] [Algebra R D] (J : Ideal D), J ^ 2 = ⊥ →
      ∀ (g : T →ₐ[R] D ⧸ J) (f : T →+* D),
      (Ideal.Quotient.mk J).comp f = g.toRingHom →
      (∀ r ∈ t, f (algebraMap R T r) = algebraMap R D r) →
      (∀ x ∈ maximalIdeal T, ∀ d : D, Ideal.Quotient.mk J d = g x →
        ∀ j ∈ J, d * j = 0) →
      ∃ δ : T →+ D, δ 1 = 0 ∧ (∀ x, δ x ∈ J) ∧
        (∀ x z, δ (x * z) = f x * δ z + f z * δ x) ∧
        ∀ r : R, δ (algebraMap R T r) =
          f (algebraMap R T r) - algebraMap R D r := by sorry

end Algebra
