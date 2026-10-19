/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.Mathlib.AlgebraicGeometry.Normalization
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer

public import Mathlib.GroupTheory.PGroup

import Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseFiltrationData
import Sheaf.AlgebraicGeometry.Curve.GenericPrimaryCoarseTraceMaps

/-!
# A primary generic filtration and its sheaf-level trace retraction

Source: blueprint `lem-sc-affine-generic-second`, proof paragraphs 1--2.
(blueprint: lem-sc-generic-primary-coarse-trace-retraction)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace AlgebraicGeometry.IsConnectedCurve

/-- A finite primary generic sheaf becomes coarsely filtered after a prime-to-primary
extension and is a retract of the finite pushforward of its filtered replacement.
The retraction is a statement about sheaves, before taking cohomology.

Source: blueprint `lem-sc-affine-generic-second`, proof paragraphs 1--2.

Proof: apply the abelian stalk/Galois-module equivalence to M. Its finite stalk is an
ell-primary discrete continuous representation. The Sylow module filtration gives an
open subgroup H of index coprime to ell and a finite H-invariant chain from zero to the
whole module. Consecutive quotients are killed by ell and H acts trivially on them.
The fixed field L of H in a separable closure is finite separable over C.functionField,
and its degree is the index of H. Replace L by an isomorphic field in Type u if needed.
Restriction of representations corresponds to inverse image along Spec L -> Spec K.
Use this correspondence and the stalk equivalence over L to transport the chain and
its short exact sequences. Each quotient has a basis over ZMod ell, giving a finite
iterated binary biproduct of the constant ZMod ell sheaf. Use F(a) equal to the terminal
term for a beyond n, so that F is defined on all natural numbers. The zero module uses
n = 0. A repeated term has quotient of dimension zero and is allowed.

Apply hmodel to L. Put D = C.normalizationIn L and pi = C.fromNormalizationIn L;
D is integral since it normalizes the integral C in a field. Transport the chain through
the supplied generic-point isomorphism. Since the stalk is finite primary, a power
ell^e annihilates M: take a maximum exponent over the finite stalk and use faithfulness
of the equivalence. Trace after restriction on M is multiplication by [L:K]. Choose
integers s,t with s*[L:K] + t*ell^e = 1. Multiplying trace by s therefore retracts
restriction. Apply generic direct image; every functor preserves the composite identity.
The compatibility in hmodel and the composition isomorphisms for direct images identify
the middle object with pi_* eta_D* F(n). Conjugate the two maps by this isomorphism to
obtain a and b with a followed by b equal to identity. No exactness or vanishing assertion
about generic direct image is needed here, and no cohomology has yet been taken.
(blueprint: lem-sc-generic-primary-coarse-trace-retraction) -/
theorem exists_generic_primary_coarse_trace_retraction
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
    (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hfinite : Finite (((Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom
        (algebraMap C.functionField (AlgebraicClosure C.functionField))))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj M))
    (hprimary : IsPGroup ℓ (Multiplicative (((Scheme.pointSmallEtale
      (Spec.map (CommRingCat.ofHom
        (algebraMap C.functionField (AlgebraicClosure C.functionField))))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj M))) :
    ∃ (D : Scheme.{u}) (π : D ⟶ C), IsFinite π ∧
      IsConnectedCurve (π ≫ f) ∧ Smooth (π ≫ f) ∧ IsAffine D ∧
      ∃ hIntegral : IsIntegral D,
      letI : IsIntegral D := hIntegral;
      ∃ (n : ℕ) (F : ℕ → Sheaf (Spec D.functionField).smallEtaleTopology
          AddCommGrpCat.{u + 1}),
        IsZero (F 0) ∧
        (∀ (a : ℕ), a < n →
          ∃ (S : ShortComplex (Sheaf (Spec D.functionField).smallEtaleTopology
              AddCommGrpCat.{u + 1})) (d : ℕ),
            S.ShortExact ∧ Nonempty (S.X₁ ≅ F a) ∧
              Nonempty (S.X₂ ≅ F (a + 1)) ∧
              Nonempty (S.X₃ ≅ Nat.rec (0 : _)
                (fun _ A ↦ A ⊞ (Spec D.functionField).constantZMod ℓ) d)) ∧
        ∃ (a : (Etale.lowerStar AddCommGrpCat.{u + 1} C.fromSpecFunctionField).obj M ⟶
            (Etale.lowerStar AddCommGrpCat.{u + 1} π).obj
              ((Etale.lowerStar AddCommGrpCat.{u + 1} D.fromSpecFunctionField).obj (F n)))
          (b : (Etale.lowerStar AddCommGrpCat.{u + 1} π).obj
              ((Etale.lowerStar AddCommGrpCat.{u + 1} D.fromSpecFunctionField).obj (F n)) ⟶
            (Etale.lowerStar AddCommGrpCat.{u + 1} C.fromSpecFunctionField).obj M),
          a ≫ b = 𝟙 _ := by
  obtain ⟨D, π, hπ, hconn, hsmooth, haff, hIntegral, n, F, hzero, hchain,
    q, hsquare, hqetale, d, hdegree, hcop, e, hkill, ⟨eterm⟩⟩ :=
    exists_generic_primary_coarse_filtration_data f hmodel M ℓ hℓ hfinite hprimary
  let : IsIntegral D := hIntegral
  let : Etale q := hqetale
  let : q.IsFiniteLocallyFreeOfDegree d := hdegree
  refine ⟨D, π, hπ, hconn, hsmooth, haff, hIntegral, n, F, hzero, hchain, ?_⟩
  exact exists_generic_primary_coarse_trace_maps π q hsquare d (ℓ ^ e)
    (hcop.pow_right e) M hkill (F n) eterm

end AlgebraicGeometry.IsConnectedCurve
