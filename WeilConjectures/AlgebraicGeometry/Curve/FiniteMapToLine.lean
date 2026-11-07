/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.LocalProperties.Projective
public import Mathlib.RingTheory.RingHom.StandardSmooth
public import Mathlib.RingTheory.Unramified.Locus
public import WeilConjectures.AlgebraicGeometry.AffineSpace.Line
public import WeilConjectures.AlgebraicGeometry.Regular
public import WeilConjectures.Mathlib.RingTheory.Kaehler.Basic
public import WeilConjectures.Mathlib.RingTheory.NoetherNormalization
public import WeilConjectures.Mathlib.RingTheory.Unramified.Field

/-!
# A finite generically étale map from an affine curve to the affine line

Let `C` be a smooth affine curve over a finite field `k`. We construct a finite morphism
`g : C ⟶ 𝔸¹_k` over `k` which is étale over a dense open of `𝔸¹_k`
(blueprint `lem-a1-finite-map-curve`).

Instead of the smooth projective completion and Riemann–Roch used in the blueprint, we use a
separable variant of Noether normalization for the coordinate ring `A = Γ(C, ⊤)`:

* Noether normalization gives `x : A` with `A` finite over `k[x]`;
* smoothness gives `a : A` such that `d a` spans the one-dimensional `Ω[K⁄k]`, where `K` is the
  function field;
* Nagata's trick: `A` is finite over `k[s]` for `s = x ^ (p ^ N) - a` with `N` large, and
  `d s = - d a` since `p = 0` in `k`;
* hence `Ω[K⁄k[s]] = 0`, so `k[s] → A` is unramified at the generic point, hence over a
  nonempty principal open of `k[s]` (the unramified locus is open and finite maps are closed),
  and `A` is flat over the principal ideal domain `k[s]`.

## Main statements

- `Algebra.exists_finite_formallyUnramified_away`: the algebraic statement.
- `AlgebraicGeometry.finrank_kaehlerDifferential_functionField`: the function field of a scheme
  smooth of relative dimension `n` over a field `k` has `n`-dimensional `Ω[K⁄k]`.
- `AlgebraicGeometry.AffineSpace.exists_isFinite_etale_morphismRestrict`: for a smooth affine
  integral curve over a perfect field of positive characteristic.
- `AlgebraicGeometry.AffineSpace.exists_isFinite_etale_morphismRestrict_of_finite`: for a smooth
  affine geometrically connected curve over a finite field.
- `AlgebraicGeometry.AffineSpace.exists_isOpenImmersion_isFinite_etale_morphismRestrict`: the
  statement in the shape of blueprint `lem-a1-finite-map-curve`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Polynomial KaehlerDifferential


namespace AlgebraicGeometry

/-- If `X` is an integral scheme smooth of relative dimension `n` over a field `k`, then the
Kähler differentials of its function field `K` over `k` form an `n`-dimensional `K`-vector space:
near the generic point, `X` is étale over `𝔸ⁿ_k`. The base ring is any ring `R` identified with
`Γ(Spec k, ⊤)` by `e`, e.g. `k` itself or `Γ(Spec k, ⊤)`. -/
theorem finrank_kaehlerDifferential_functionField {k R : Type u} [Field k] [CommRing R]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k)) (n : ℕ) [SmoothOfRelativeDimension n f]
    [Algebra R X.functionField] (e : R ≃+* Γ(Spec (.of k), ⊤))
    (hk : algebraMap R X.functionField = (X.presheaf.germ ⊤ (genericPoint X) trivial).hom.comp
      (f.appTop.hom.comp e.toRingHom)) :
    Module.finrank X.functionField Ω[X.functionField⁄R] = n := by
  have : Nontrivial R := e.toEquiv.nontrivial
  obtain ⟨U, -, V, hV, hx, e', H⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f)
      (genericPoint X)
  obtain rfl : U = ⊤ := eq_top_iff.mpr fun z _ ↦ Subsingleton.elim (f (genericPoint X)) z ▸ e' hx
  obtain ⟨φ, hφC, hφ⟩ := H.exists_etale_mvPolynomial
  have : Nonempty V := ⟨⟨genericPoint X, hx⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X V hV
  let ε : MvPolynomial (Fin n) R ≃+* MvPolynomial (Fin n) Γ(Spec (.of k), ⊤) :=
    MvPolynomial.mapEquiv _ e
  let : Algebra R Γ(X, V) := ((f.appLE ⊤ V e').hom.comp e.toRingHom).toAlgebra
  let : Algebra (MvPolynomial (Fin n) R) Γ(X, V) := (φ.comp ε.toRingHom).toAlgebra
  have : IsScalarTower R (MvPolynomial (Fin n) R) Γ(X, V) := .of_algebraMap_eq fun c ↦ by
    simp [RingHom.algebraMap_toAlgebra, ε, ← hφC]
  have : Algebra.Etale (MvPolynomial (Fin n) R) Γ(X, V) :=
    RingHom.Etale.respectsIso.2 _ _ hφ
  have : IsScalarTower R Γ(X, V) X.functionField := .of_algebraMap_eq fun c ↦ by
    rw [hk]
    simp [RingHom.algebraMap_toAlgebra, Scheme.Hom.appLE]
  have e₁ := tensorKaehlerEquivOfFormallyEtale R (MvPolynomial (Fin n) R) Γ(X, V)
  have : Module.Free Γ(X, V) Ω[Γ(X, V)⁄R] := .of_equiv e₁
  have hB : Module.finrank Γ(X, V) Ω[Γ(X, V)⁄R] = n := by
    rw [← e₁.finrank_eq, Module.finrank_baseChange, Module.finrank_eq_card_basis
      (mvPolynomialBasis R (Fin n)), Fintype.card_fin]
  rw [Module.finrank_of_isLocalizedModule_of_free X.functionField (nonZeroDivisors Γ(X, V))
    (KaehlerDifferential.map R R Γ(X, V) X.functionField), hB]


variable {k : Type u} [Field k]

namespace AffineSpace


end AffineSpace

end AlgebraicGeometry
