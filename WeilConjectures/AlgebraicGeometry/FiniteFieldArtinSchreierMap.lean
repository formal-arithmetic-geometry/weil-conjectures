/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.ArtinSchreier
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.FieldTheory.Finite.Basic
import WeilConjectures.Mathlib.Algebra.CharP.Lemmas
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Limits

/-!
# The finite-field Artin–Schreier map

Source: literature/blueprint/latest/blueprint/sec-fourier-transform/sk-lem-as-properties/
lem-wft-as-comparison.proof.md, Proof (2) (blueprint: lem-wft-finite-field-as-map)

The finite-field specialization of the affine-line Artin–Schreier map is finite étale,
surjective, translation-invariant, and trivialized by the translations indexed by the field.
-/

@[expose] public section

universe u

open CategoryTheory Limits
open AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.AffineSpace

/-- For a finite field `k`, the map `t ↦ t ^ |k| - t` on the affine line is finite étale and
  surjective, invariant under translations by `k`, and its canonical translation torsor map is an
  isomorphism. This is the finite-field affine-line torsor assertion in the proof of the
  Artin–Schreier comparison (blueprint: lem-wft-finite-field-as-map).

  Source: current blueprint, `lem-wft-as-comparison.proof.md`, Proof (2).
  Proof (the node's seven steps):
  1. Write `q = p ^ a`. Present the coordinate algebra as `k[u][T]/(T ^ q - T - u)`.
     It is finite free by `lem-weil-pbc-monic-quotient-free`; the affine-morphism lemma
     `lem-weil-pbc-morphism-affine-schemes-affine` then gives finiteness by
     `def-weil-finite-integral-morphism`.
  2. Its derivative is `-1`; apply `lem-weil-pbc-standard-etale-monic-derivative` to
     obtain étaleness and hence the finite étale property.
  3. By `lem-weil-finite-field-pow-card` and `def-weil-ring-frobenius`, the polynomial
     is invariant under translation. Contravariance of `def-weil-affine-spectrum`
     gives the translation identity.
  4. Above any prime of `k[u]`, pass to an algebraic closure of its fraction residue field
     (`def-weil-algebraic-closure`) and choose a root of `T ^ q - T - b`. Its kernel is
     a prime over the given prime, proving surjectivity on scheme points.
  5. By `lem-weil-pbc-fibre-product-affine-spectra`, the self-pullback is
     `k[x][Y]/(Y ^ q - Y - (x ^ q - x))`.
  6. The roots `Y = x + c` for `c ∈ k` differ by units. The evaluation lemma
     `lem-pur-monic-unit-difference-evaluation` identifies this algebra with the product
     of `k[x]` indexed by `k`.
  7. By `lem-weil-pbc-finite-affine-coproduct-spectrum`, its spectrum is the coproduct
     in the statement. The two projections on the summand `c` are identity and
     translation by `c`; uniqueness in `def-pc-fibre-product` identifies the map.

  (blueprint: lem-wft-finite-field-as-map) -/
theorem finiteField_artinSchreier_map (k : Type u) [Field k] [Fintype k] :
    IsFinite (artinSchreierMap PUnit.{u + 1} (Spec (.of k)) (Fintype.card k)) ∧
      Etale (artinSchreierMap PUnit.{u + 1} (Spec (.of k)) (Fintype.card k)) ∧
      Function.Surjective
        (artinSchreierMap PUnit.{u + 1} (Spec (.of k)) (Fintype.card k)).base ∧
      (∀ c : k,
        translation (fun _ : PUnit.{u + 1} ↦ (Scheme.ΓSpecIso (.of k)).inv.hom c) ≫
            artinSchreierMap PUnit.{u + 1} (Spec (.of k)) (Fintype.card k) =
          artinSchreierMap PUnit.{u + 1} (Spec (.of k)) (Fintype.card k)) ∧
      IsIso (artinSchreierTorsorMap (n := PUnit.{u + 1}) (S := Spec (.of k)) k
        (Scheme.ΓSpecIso (.of k)).inv.hom) := by
  sorry

end AlgebraicGeometry.AffineSpace

end
