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

import Sheaf.AlgebraicGeometry.Curve.GenericFinitePrimaryDecomposition
import Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseTraceRetraction
import WeilConjectures.AlgebraicGeometry.Sites.CohomologyClopen

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
          Function.Injective j := by
  classical
  obtain ⟨r, p, N, hp, hNfinite, hNprimary, a, b, hab⟩ :=
    Scheme.exists_finite_primary_sheaf_decomposition C.functionField M hM hfinite
  have hdata (i : Fin r) :=
    exists_generic_primary_coarse_trace_retraction f hmodel (N i) (p i) (hp i)
      (hNfinite i) (hNprimary i)
  choose D π hπ hconn hsmooth haffine hIntegral n F hzero hstep α β hαβ using hdata
  let : ∀ i, IsIntegral (D i) := hIntegral
  let : ∀ i, IsFinite (π i) := hπ
  let P := Etale.lowerStar AddCommGrpCat.{u + 1} C.fromSpecFunctionField
  let G (i : Fin r) :=
    (Etale.lowerStar AddCommGrpCat.{u + 1} (D i).fromSpecFunctionField).obj (F i (n i))
  let edge (i : Fin r) :
      Sheaf.H ((Etale.lowerStar AddCommGrpCat.{u + 1} (π i)).obj (G i)) 2 →
        Sheaf.H (G i) 2 :=
    fun x ↦ Sheaf.H.map
      ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (π i)).counit.app (G i)) 2
        (Etale.cohomologyMap (π i) _ 2 x)
  have hedge (i : Fin r) : Function.Injective (edge i) :=
    (Etale.bijective_edgeMap_of_isFinite (π i) (G i) 2).injective
  refine ⟨r, D, fun i ↦ π i ≫ f, hconn, hsmooth, haffine, hIntegral,
    n, F, hzero, ?_, ?_⟩
  · intro i t ht
    obtain ⟨S, d, hS, he₁, he₂, he₃⟩ := hstep i t ht
    exact ⟨S, p i, d, hp i, hS, he₁, he₂, he₃⟩
  · refine ⟨fun x i ↦ edge i (Sheaf.H.map (α i) 2 (Sheaf.H.map (P.map (a i)) 2 x)), ?_⟩
    intro x y hxy
    have hcomponent (i : Fin r) :
        Sheaf.H.map (P.map (a i)) 2 x = Sheaf.H.map (P.map (a i)) 2 y := by
      have hi := hedge i (congrFun hxy i)
      have hi' := congrArg (Sheaf.H.map (β i) 2) hi
      simpa only [← Sheaf.H.map_comp_apply, hαβ i, Sheaf.H.map_id_apply] using hi'
    have hsum : ∑ i, P.map (a i) ≫ P.map (b i) = 𝟙 (P.obj M) := by
      calc
        _ = P.map (∑ i, a i ≫ b i) := by
          rw [P.map_sum]
          simp_rw [P.map_comp]
        _ = P.map (𝟙 M) := congrArg P.map hab
        _ = 𝟙 (P.obj M) := P.map_id M
    have hR := congrArg (Sheaf.functorH C.smallEtaleTopology 2).map hsum
    simp only [Functor.map_sum, Functor.map_comp] at hR
    have hvalue := congrArg (fun z ↦ z x) hR
    have hvalue' := congrArg (fun z ↦ z y) hR
    have heval (z : Sheaf.H (P.obj M) 2) :
        (∑ i, (Sheaf.functorH C.smallEtaleTopology 2).map (P.map (a i)) ≫
          (Sheaf.functorH C.smallEtaleTopology 2).map (P.map (b i))) z =
        ∑ i, Sheaf.H.map (P.map (b i)) 2 (Sheaf.H.map (P.map (a i)) 2 z) := by
      change (AddCommGrpCat.homAddEquiv (∑ i,
        (Sheaf.functorH C.smallEtaleTopology 2).map (P.map (a i)) ≫
          (Sheaf.functorH C.smallEtaleTopology 2).map (P.map (b i)))) z = _
      rw [map_sum]
      rw [AddMonoidHom.finsetSum_apply]
      rfl
    have hx : (∑ i, Sheaf.H.map (P.map (b i)) 2
        (Sheaf.H.map (P.map (a i)) 2 x)) = x := by
      rw [← heval]
      exact hvalue.trans (Sheaf.H.map_id_apply x)
    have hy : (∑ i, Sheaf.H.map (P.map (b i)) 2
        (Sheaf.H.map (P.map (a i)) 2 y)) = y := by
      rw [← heval]
      exact hvalue'.trans (Sheaf.H.map_id_apply y)
    rw [← hx, ← hy]
    apply Finset.sum_congr rfl
    intro i hi
    exact congrArg (Sheaf.H.map (P.map (b i)) 2) (hcomponent i)

end AlgebraicGeometry.IsConnectedCurve
