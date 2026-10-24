/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.FibreModel

/-!

# Affine models embed into proper models

Let `Φ` be the model Frobenius of an affine model `X₀` of `X = X₀ ×_{k₀} k`, of finite type over
the finite field `k₀`. An immersion `X₀ ⟶ ℙ^N_{k₀}` over `k₀`
(`AlgebraicGeometry.exists_isImmersion_projectiveSpace`) base changes to a morphism `f : X ⟶ Y`
to the proper scheme `Y = ℙ^N_k` with its model Frobenius, commuting with the model Frobenii,
whose fibres over the rational points of `Y` are empty or a point, hence proper (blueprint
`thm-trf-coefficient-morphism-trace-formula`, Steps 2–4, where the compactification of the affine
line plays this role).

## Main results

- `ProEtale.CondensedRing.IsModelFrobenius.exists_isProper_pullback`: an affine model embeds
  into a proper model, with proper fibres.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {Φ : X ⟶ X}
  {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀}

/-- **An affine model embeds into a proper model** (blueprint
`thm-trf-coefficient-morphism-trace-formula`, Steps 2–4): for the model Frobenius `Φ` of an
affine model `X₀` of finite type over `k₀`, there are a proper `Y` over `k` with the model
Frobenius `Φ_Y` of a model `Y₀` of finite type over `k₀` and a morphism `f : X ⟶ Y`, the base
change of a `k₀`-morphism `f₀ : X₀ ⟶ Y₀`, with `Φ ≫ f = f ≫ Φ_Y`, whose fibres over the rational
points of `Y` are proper over `k`. -/
theorem IsModelFrobenius.exists_isProper_pullback [IsAlgClosed k] [LocallyOfFiniteType f₀]
    [IsAffine X₀] (hΦ : IsModelFrobenius Φ f₀ p) :
    ∃ (Y : Over (Spec (.of k))) (_ : LocallyOfFiniteType Y.hom) (_ : QuasiCompact Y.hom)
      (_ : IsSeparated Y.hom) (Y₀ : Scheme.{u}) (fY₀ : Y₀ ⟶ Spec (.of k₀)) (pY : Y.left ⟶ Y₀)
      (ΦY : Y ⟶ Y) (f : X ⟶ Y) (f₀' : X₀ ⟶ Y₀),
      IsProper Y.hom ∧ LocallyOfFiniteType fY₀ ∧ IsModelFrobenius ΦY fY₀ pY ∧
        Φ ≫ f = f ≫ ΦY ∧ f.left ≫ pY = p ≫ f₀' ∧ f₀' ≫ fY₀ = f₀ ∧
        ∀ y : RationalPoint Y, IsProper (pullback f y).hom :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
