/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.ProEtaleFiniteLocallyProjective

/-! # Constructibility of finite locally projective coefficients

A component of the local finite projective model proposition. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing

namespace WeilConjectures.CondensedPoincareDualityConventions

/-- Finite locally projective coefficient modules are constant-model constructible.

Source: latest blueprint, sec-six-functors/sk-def-ops,
prop-pod-perfect-local-model.proof.md, constructibility paragraph; Stacks Tag 093U.
(blueprint: lem-pod-perfect-local-model-constructible).

Proof in words. The finite discrete coefficient comparison identifies the pulled-back
coefficient sheaf with the constant sheaf of the finite discrete commutative ring A, compatibly with
restriction. On each covering member in the local-projective hypothesis choose a
finite free retract with inclusion i and retraction p, so i followed by p is the
identity of P. The endomorphism e of the finite free module given by p followed by i
is idempotent, and i identifies P with ker(1-e): if e x = x then x = i(p x), and
(1-e)i = 0. The kernel part of the locally constant finite-type Serre theorem over
the Noetherian finite coefficient ring makes P locally constant of finite type on
that covering member. Compose its trivializing covers with the original covering.
Every finitely generated module over this finite ring is finite. Thus the one-stratum
partition of X supplies the finite-stalk constructibility predicate, transported
back to native constant-model coordinates by the coefficient comparison. Zero ranks
and the empty scheme are included by the same kernel and covering argument. -/
theorem perfect_local_model_constructible (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [DiscreteTopology A] [Finite A]
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X] :
    let Λ := Profinite.continuousCoefficientRingObj A
    ∀ P : supportModules Λ X, IsFiniteLocallyProjective Λ X P →
      IsConstantModelConstructible Λ X P := by
  sorry

end WeilConjectures.CondensedPoincareDualityConventions
