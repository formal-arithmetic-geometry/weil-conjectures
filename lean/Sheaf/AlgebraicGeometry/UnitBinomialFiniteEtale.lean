/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N9
-/
module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import WeilConjectures.Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale

/-! # The finite etale algebra obtained by taking a root of a unit

Source: Stacks Project, Tag 03PL, `lemma-kummer-sequence`, proof on an affine open
(blueprint: lem-sfb-unit-binomial-finite-etale).

The quotient is Mathlib's `AdjoinRoot`, with its canonical quotient algebra structure.
The basis is indexed by `Fin n`, including over the zero ring.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

/-- Adjoining an `n`th root of a unit gives the indicated power basis and a finite,
surjective, etale morphism of spectra, also for the zero ring and for `n = 1`.
Source: Stacks Project, Tag 03PL, `lemma-kummer-sequence`, affine unit-root construction
(blueprint: lem-sfb-unit-binomial-finite-etale).

Proof (the seven steps of the reviewed DAG proof):
1. If `R` is the zero ring, the polynomial ring and its quotient are zero rings. The
   coordinate map from `R^n` to the quotient is the unique isomorphism between singleton
   modules, giving the stated basis (def-weil-pbc-free-module). Both spectra are empty
   (def-weil-affine-spectrum), so the map is surjective (def-weil-surjective-morphism).
   It is finite by lem-weil-pbc-spec-finite-ring-map-finite and etale by the empty affine
   cover in def-weil-etale-morphism. For the remaining steps assume `R` is nonzero.
2. The polynomial `f = X^n - C u` is monic of degree `n`, since `1 <= n` and `1` is nonzero.
   By lem-weil-pbc-monic-quotient-free its quotient has basis the powers `t^i` for `i < n`.
   This also makes the quotient a finite `R`-module.
3. Apply lem-weil-pbc-spec-finite-ring-map-finite to the canonical structure map and the
   module finiteness from step 2 to obtain finiteness of its spectrum map.
4. For any `R`-module `N`, the basis coordinates give mutually inverse maps between
   `B` tensor `N` and `N^n`: send `b` tensor `x` to `(c_i(b) x)_i`, and send `(x_i)_i`
   to the sum of `t^i` tensor `x_i`. Tensoring a map corresponds to its componentwise
   `n`-fold product. Exactness is preserved componentwise and reflected by inserting
   an element in coordinate zero, lifting it, and projecting back to coordinate zero.
   This coordinate exists because `1 <= n`. Thus the structure map is faithfully flat
   by def-weil-pbc-faithfully-flat-ring-map (Stacks Tag 00HB).
5. Apply lem-weil-pbc-faithfully-flat-surjective-spectrum (Tag 00HQ) to get surjectivity
   on primes, hence surjectivity of the scheme morphism (def-weil-surjective-morphism).
6. In the quotient, `t^n = u`. If `v` is the image of the inverse of `u`, then
   `t * (v * t^(n-1)) = 1`. If `a` is the image of the inverse of `n`, the derivative
   `n * t^(n-1)` has inverse `a * (v * t^(n-1))^(n-1)`. These are identities in the
   polynomial quotient (def-weil-polynomial-ring, def-weil-pbc-algebra-hom-quotient).
7. By lem-weil-pbc-standard-etale-monic-derivative (Tags 00UB and 00UC), the standard
   etale algebra `C = R[T,Y]/(f, Y*f' - 1)` has etale spectrum over `R`. Its universal
   property gives a map to `B` sending `T` to `t` and `Y` to the inverse derivative.
   The relation `f(T) = 0` gives a map back. The composite on `B` fixes constants and `t`.
   The composite on `C` fixes constants and `T`, and fixes `Y` by uniqueness of inverses
   of `f'(T)`. They are inverse algebra maps (def-weil-pbc-algebra-hom-quotient).
   Contravariant spectra (def-weil-affine-spectrum) identify the structure morphisms,
   so the affine-local definition def-weil-etale-morphism gives etaleness for `B`.
-/
theorem unitBinomial_finite_surjective_etale (R : Type u) [CommRing R]
    (n : ℕ) (hn : 1 ≤ n) (hnR : IsUnit (n : R)) (u : Rˣ) :
    (∃ b : Module.Basis (Fin n) R
      (AdjoinRoot (Polynomial.X ^ n - Polynomial.C (u : R))),
      ∀ i : Fin n,
        b i = AdjoinRoot.root (Polynomial.X ^ n - Polynomial.C (u : R)) ^ (i : ℕ)) ∧
    IsFinite (Spec.map (CommRingCat.ofHom
      (algebraMap R (AdjoinRoot (Polynomial.X ^ n - Polynomial.C (u : R)))))) ∧
    Surjective (Spec.map (CommRingCat.ofHom
      (algebraMap R (AdjoinRoot (Polynomial.X ^ n - Polynomial.C (u : R)))))) ∧
    Etale (Spec.map (CommRingCat.ofHom
      (algebraMap R (AdjoinRoot (Polynomial.X ^ n - Polynomial.C (u : R)))))) := by
  classical
  have hn₀ : n ≠ 0 := Nat.ne_of_gt hn
  have hf := Polynomial.monic_X_pow_sub_C (u : R) hn₀
  have hb : ∃ b : Module.Basis (Fin n) R
      (AdjoinRoot (Polynomial.X ^ n - Polynomial.C (u : R))),
      ∀ i : Fin n,
        b i = AdjoinRoot.root (Polynomial.X ^ n - Polynomial.C (u : R)) ^ (i : ℕ) := by
    rcases subsingleton_or_nontrivial R with hR | hR
    · let := hR
      let := Module.subsingleton R
        (AdjoinRoot (Polynomial.X ^ n - Polynomial.C (u : R)))
      exact ⟨default, fun _ ↦ Subsingleton.elim _ _⟩
    · let := hR
      let pb := AdjoinRoot.powerBasis' hf
      have hd : pb.dim = n := Polynomial.natDegree_X_pow_sub_C
      refine ⟨pb.basis.reindex (finCongr hd), ?_⟩
      intro i
      rw [Module.Basis.reindex_apply, pb.basis_eq_pow]
      rfl
  have hdeg : (Polynomial.X ^ n - Polynomial.C (u : R)).degree ≠ 0 := by
    nontriviality R
    rw [Polynomial.degree_X_pow_sub_C hn]
    exact_mod_cast hn₀
  have := hf.finite_adjoinRoot
  refine ⟨hb, ?_, ?_, ?_⟩
  · rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  · exact ((flat_and_surjective_SpecMap_iff _).mpr
      (RingHom.faithfullyFlat_algebraMap_iff.mpr
        (AdjoinRoot.faithfullyFlat_of_monic hf hdeg))).2
  · rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr (AdjoinRoot.etale_X_pow_sub_C hn₀ hnR u.isUnit)

end AlgebraicGeometry
