/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleTorsion
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer

import Sheaf.AlgebraicGeometry.AbelianSheavesGModules
import Sheaf.RepresentationTheory.SylowModuleFiltration
import Sheaf.FieldTheory.OpenSubgroupFixedField
import Sheaf.AlgebraicGeometry.FiniteEtaleTrace
import Sheaf.AlgebraicGeometry.FiniteEtaleTraceDegree
import WeilConjectures.SixFunctors.Finite.GlobalSections
import WeilConjectures.SixFunctors.Finite.Exact

/-!
# Generic finite trace with unrefined constant-vector-space quotients

Source: blueprint `lem-sc-affine-generic-second`, proof paragraphs 1--2.
(blueprint: lem-sc-generic-finite-coarse-trace-filtration-data)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace AlgebraicGeometry.IsConnectedCurve

/-- Finite primary summands admit coarse generic filtrations whose quotients are finite
iterated binary direct sums of prime constant sheaves, with an injection on second cohomology.
This construction leaves the basis-flag refinement to a separate proved categorical lemma.

Source: blueprint `lem-sc-affine-generic-second`, proof paragraphs 1--2.

Proof: use the stalk/Galois-module equivalence to identify M with a finite discrete module.
Its finite primary decomposition is Galois invariant. For each nonzero primary summand choose
an open subgroup of index prime to its prime using the Sylow module filtration theorem.
The invariant chain supplied there has finite quotients killed by that prime and with trivial
subgroup action. Each quotient is a finite-dimensional vector space over the prime field;
choose a basis to identify it with a finite direct sum of constants, without refining the
chain by the basis flag. The open subgroup determines a finite separable fixed field L,
which can be shrunk to the base universe. Transport the chain to sheaves on Spec L.
Normalize C in L using hmodel, transporting the sheaves to its identified generic point.
This normalization is integral since C is integral and L is a field.

Restriction followed by trace on each primary summand is multiplication by the extension
degree. This degree is prime to an annihilating primary exponent, so Bezout gives an inverse
scalar on that summand and hence a retraction of restriction. Apply generic direct image and
second cohomology: a split monomorphism stays split under any functor. Compatibility of the
generic inclusions with normalization identifies the result with finite direct image from
the normalization. Exact finite direct image and the finite pushforward cohomology comparison
identify its cohomology with the displayed H² on D. Finite primary decomposition and
additivity of direct image and cohomology combine these injections into the product injection.
A zero stalk gives the zero sheaf by the equivalence and uses r = 0. Zero-dimensional
quotients are allowed, and the initial terms are zero. No vanishing hypothesis is used.
(blueprint: lem-sc-generic-finite-coarse-trace-filtration-data) -/
theorem exists_generic_finite_coarse_trace_filtration_data
    {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}
    (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C] [IsIntegral C]
    (hmodel : ∀ (L : Type u) [Field L] [Algebra C.functionField L]
      [FiniteDimensional C.functionField L],
      IsFinite (C.fromNormalizationIn L) ∧ IsAffine (C.normalizationIn L) ∧
        IsConnectedCurve (C.fromNormalizationIn L ≫ f) ∧
        Smooth (C.fromNormalizationIn L ≫ f) ∧
        ∃ e : Spec (.of L) ≅ Spec (C.normalizationIn L).functionField,
          e.hom ≫ (C.normalizationIn L).fromSpecFunctionField =
            (C.fromSpecOfAlgebraFunctionField L).toNormalization)
    (M : Sheaf (Spec C.functionField).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hM : M.IsTorsion)
    (hfinite : Finite (((Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom
        (algebraMap C.functionField (AlgebraicClosure C.functionField))))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj M)) :
    ∃ (r : ℕ) (D : Fin r → Scheme.{u}) (g : ∀ i, D i ⟶ Spec (.of k)),
      (∀ i, IsConnectedCurve (g i)) ∧ (∀ i, Smooth (g i)) ∧
      (∀ i, IsAffine (D i)) ∧
      ∃ hIntegral : ∀ i, IsIntegral (D i),
      letI : ∀ i, IsIntegral (D i) := hIntegral;
      ∃ (n : Fin r → ℕ)
        (F : ∀ i, ℕ → Sheaf (Spec (D i).functionField).smallEtaleTopology
          AddCommGrpCat.{u + 1}),
        (∀ i, IsZero (F i 0)) ∧
        (∀ i (a : ℕ), a < n i →
          ∃ (S : ShortComplex (Sheaf (Spec (D i).functionField).smallEtaleTopology
              AddCommGrpCat.{u + 1})) (ℓ d : ℕ),
            ℓ.Prime ∧ S.ShortExact ∧ Nonempty (S.X₁ ≅ F i a) ∧
              Nonempty (S.X₂ ≅ F i (a + 1)) ∧
              Nonempty (S.X₃ ≅ Nat.rec (0 : _)
                (fun _ A ↦ A ⊞ (Spec (D i).functionField).constantZMod ℓ) d)) ∧
        ∃ j : Sheaf.H
          ((Etale.lowerStar AddCommGrpCat.{u + 1} C.fromSpecFunctionField).obj M) 2 →
          ∀ i, Sheaf.H
            ((Etale.lowerStar AddCommGrpCat.{u + 1} (D i).fromSpecFunctionField).obj
              (F i (n i))) 2,
          Function.Injective j := by sorry

end AlgebraicGeometry.IsConnectedCurve
