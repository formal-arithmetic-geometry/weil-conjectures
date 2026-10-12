/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.LinearAlgebra.Charpoly.Basic
public import WeilConjectures.ZetaLinearAlgebra.FrobeniusModule.Map

/-!
# Short exact sequences of Frobenius modules

For a short exact sequence `0 → V' → V → V'' → 0` of Frobenius modules with Frobenius-equivariant
maps, the characteristic polynomial of the Frobenius of `V` is the product of those of `V'` and
`V''`: in a basis of `V` extending one of `V'` the Frobenius matrix is block upper triangular.
Hence the spectrum of `V` (the multiset of the images under `ι` of its eigenvalues, with
algebraic multiplicity) is the sum of the spectra of `V'` and `V''`.

As a consequence an upper weight bound passes to Frobenius-stable subquotients.

## Main results

- `FrobeniusModule.charpoly_frobeniusEnd_eq_mul`: multiplicativity of the characteristic
  polynomial along a short exact sequence.
- `FrobeniusModule.roots_charpoly_frobeniusEnd_map_eq_add`: additivity of the spectrum.
- `FrobeniusModule.HasWeightsAtMost.of_subquotient`: weights of subquotients.
-/

@[expose] public section

universe u v

open Polynomial

namespace FrobeniusModule

variable {K : Type v} [Field K]

section Exact

variable {M' M M'' : FrobeniusModule.{u, v} K}
  (f : M'.carrier →ₗ[K] M.carrier) (g : M.carrier →ₗ[K] M''.carrier)
  (hf : ∀ x, f (M'.frobenius x) = M.frobenius (f x))
  (hg : ∀ x, g (M.frobenius x) = M''.frobenius (g x))

include hf hg in
/-- *Spectrum of an exact Frobenius sequence*, characteristic polynomials: for a short exact
sequence `0 → V' → V → V'' → 0` of Frobenius modules with Frobenius-equivariant maps,
`χ_V = χ_{V'} χ_{V''}`. The image of `V'` is a Frobenius-stable subspace of `V`, isomorphic to
`V'`, with quotient isomorphic to `V''`, so this is
`LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ`.
(blueprint: `lem-a1-spectrum-exact-sequence`) -/
theorem charpoly_frobeniusEnd_eq_mul (hinj : Function.Injective f)
    (hsurj : Function.Surjective g) (hexact : Function.Exact f g) :
    M.frobeniusEnd.charpoly = M'.frobeniusEnd.charpoly * M''.frobeniusEnd.charpoly := by
  set W : Submodule K M.carrier := LinearMap.range f
  have hW : W ≤ W.comap M.frobeniusEnd := by
    rintro _ ⟨x, rfl⟩
    exact ⟨M'.frobenius x, hf x⟩
  rw [LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ _ W hW]
  congr 1
  · -- the restriction to `W = f(V')` is conjugate to the Frobenius of `V'`
    refine (LinearMap.charpoly_eq_of_comp_eq (LinearEquiv.ofInjective f hinj) ?_).symm
    ext x
    exact hf x
  · -- the quotient `V ⧸ W` is identified with `V''` by `g`
    have hker : LinearMap.ker g = W := by
      ext x
      exact (hexact x).trans (by rfl)
    let e : (M.carrier ⧸ W) ≃ₗ[K] M''.carrier :=
      (Submodule.quotEquivOfEq _ _ hker.symm).trans (g.quotKerEquivOfSurjective hsurj)
    refine LinearMap.charpoly_eq_of_comp_eq e ?_
    ext x
    exact hg x

include hf hg in
/-- *Spectrum of an exact Frobenius sequence*: for a short exact sequence `0 → V' → V → V'' → 0`
of Frobenius modules with Frobenius-equivariant maps, the spectrum of `V` — the multiset of the
images under `ι : K →+* ℂ` of the eigenvalues of its Frobenius, counted with algebraic
multiplicity — is the sum of the spectra of `V'` and `V''`.
(blueprint: `lem-a1-spectrum-exact-sequence`) -/
theorem roots_charpoly_frobeniusEnd_map_eq_add (ι : K →+* ℂ) (hinj : Function.Injective f)
    (hsurj : Function.Surjective g) (hexact : Function.Exact f g) :
    (M.frobeniusEnd.charpoly.map ι).roots =
      (M'.frobeniusEnd.charpoly.map ι).roots + (M''.frobeniusEnd.charpoly.map ι).roots := by
  rw [charpoly_frobeniusEnd_eq_mul f g hf hg hinj hsurj hexact, Polynomial.map_mul,
    Polynomial.roots_mul]
  exact mul_ne_zero ((M'.frobeniusEnd.charpoly_monic.map ι).ne_zero)
    ((M''.frobeniusEnd.charpoly_monic.map ι).ne_zero)

end Exact


/-- *Subquotient bounds for Frobenius modules*: if `(V, F)` has weights at most `w`, then so
has every Frobenius-stable subquotient of `V`, presented as a Frobenius-equivariant quotient
`A ↠ S` of a Frobenius-equivariant subspace `A ↪ V`.
(blueprint: `lem-a1-subquotient-extension-bounds`) -/
theorem HasWeightsAtMost.of_subquotient {V A S : FrobeniusModule.{u, v} K}
    (i : A.carrier →ₗ[K] V.carrier) (hi : ∀ x, i (A.frobenius x) = V.frobenius (i x))
    (hinj : Function.Injective i) (p : A.carrier →ₗ[K] S.carrier)
    (hp : ∀ x, p (A.frobenius x) = S.frobenius (p x)) (hsurj : Function.Surjective p)
    {ι : K →+* ℂ} {q : ℕ} {w : ℝ} (h : V.HasWeightsAtMost ι q w) :
    S.HasWeightsAtMost ι q w :=
  (h.of_injective i hi hinj).of_surjective p hp hsurj

end FrobeniusModule
