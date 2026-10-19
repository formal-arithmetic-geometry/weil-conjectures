/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q145
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.ConstructibleTopology

/-!
# Finite prime-to-ell decomposed étale subfamilies

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé II, Corollary 2.2.4,
printed p. 27, for a prime ell, using Proposition 2.2.2, printed pp. 26--27
(blueprint: lem-per-prime-to-ell-decomposed-etale-finite-subcover).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry

/-- A prime-to-ell decomposed étale family over a Noetherian scheme contains a finite
subfamily with the same pointwise lifting property. The sources need not be quasi-compact
or separated. Source: ILO, Travaux de Gabber, Exposé II, Corollary 2.2.4, printed p. 27
(blueprint: lem-per-prime-to-ell-decomposed-etale-finite-subcover).

Proof:
1. The finite affine Noetherian cover makes `X` quasi-compact and locally Noetherian
   (`pqf-def-locnoeth`). The closed-subset minimality lemma
   (`lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`) gives the descending-chain
   condition, so every subset is quasi-compact (`lem-sfb-noetherian-space-compact-subsets`).
   Local Noetherianity gives quasi-separatedness
   (`lem-weil-pbc-locally-noetherian-quasi-separated`), hence the underlying space is spectral
   (`lem-weil-pbc-qcqs-scheme-spectral`). Its constructible topology is quasi-compact
   (`lem-weil-pbc-spectral-constructible-topology-quasi-compact`).
2. For each `i`, let `C_i` consist of the points with a lift through `f i` of finite residue
   degree prime to `ell` (`def-weil-etale-morphism`, `def-weil-residue-field`). By ILO II
   Proposition 2.2.2 (`lem-per-prime-to-ell-decomposed-locus-constructible`), this locus is
   ind-constructible, hence open in the constructible topology. No quasi-compactness or
   separation of `U i` is used.
3. The hypothesis says that these loci cover `X`. Constructible compactness
   (`lem-weil-pbc-spectral-constructible-topology-quasi-compact`) selects finitely many
   indices. Unfolding their loci gives exactly the required lifts and residue degrees.
   If `X` is empty, choose the empty subset of indices. -/
theorem primeToEllDecomposed_etale_finite_subcover
    (X : Scheme.{u}) [IsNoetherian X] (ell : ℕ) (hell : ell.Prime) {I : Type w}
    (U : I → Scheme.{u}) (f : ∀ i : I, U i ⟶ X)
    (het : ∀ i : I, Etale (f i))
    (hcover : ∀ x : X, ∃ (i : I) (z : U i),
      f i z = x ∧ ((f i).residueFieldMap z).hom.Finite ∧
        Nat.Coprime ((f i).residueDegree z) ell) :
    ∃ I₀ : Set I, I₀.Finite ∧ ∀ x : X, ∃ i ∈ I₀, ∃ z : U i,
      f i z = x ∧ ((f i).residueFieldMap z).hom.Finite ∧
        Nat.Coprime ((f i).residueDegree z) ell := by
  sorry

end AlgebraicGeometry
