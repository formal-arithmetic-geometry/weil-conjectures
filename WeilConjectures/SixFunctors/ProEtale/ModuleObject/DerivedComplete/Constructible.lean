/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.DerivedComplete.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionConstructible

/-!
# Bounded constructible `𝒪_E`-complexes are derived complete

On a noetherian scheme `X`, every bounded constructible complex of `𝒪_{E,X}`-module objects is
derived complete (`ProEtale.derivedCompleteIntegers_of_boundedConstructible`, part of blueprint
`sk-prop-integral-criterion`).

By dévissage along the truncation triangles, it suffices to treat a constructible module object
`M` placed in one degree. For it, derived completeness follows from the bijectivity of
`1 - ϖ · shift : ∏ₙ M ⟶ ∏ₙ M`, which is checked after pullback to finitely many affine members
of pro-étale covers of the strata (the pullbacks preserve countable products), where `M` is
finitely presented. A finitely presented module is a cokernel of a map of finite free modules,
and the bijectivity passes to cokernels by the snake lemma; for `𝒪_{E,V}` itself it is the
`ϖ`-adic completeness of the rings `C(V, 𝒪_E)` of sections.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

open Scheme PadicAlgCl CondensedRing

variable {ℓ : ℕ} [Fact ℓ.Prime] {E : FiniteIntermediateField ℓ}

/-- On a noetherian scheme, **bounded constructible `𝒪_E`-complexes are derived complete**
(part of blueprint `sk-prop-integral-criterion`). -/
theorem derivedCompleteIntegers_of_boundedConstructible {X : Scheme.{u}} [IsNoetherian X]
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X))}
    (hK : boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X) K) :
    derivedCompleteIntegers ℓ E X K :=
  sorry

end AlgebraicGeometry.ProEtale
