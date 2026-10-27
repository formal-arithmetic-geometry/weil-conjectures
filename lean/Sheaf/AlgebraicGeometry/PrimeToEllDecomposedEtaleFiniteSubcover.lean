/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NW
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.ConstructibleTopology

/-!
# Finite extraction for prime-to-ell decomposed étale families

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé II, Corollary 2.2.4,
printed p. 27, using Proposition 2.2.2, printed p. 26
(blueprint: lem-per-prime-to-ell-decomposed-etale-finite-subcover).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry

/-- A prime-to-ell decomposed étale family over a Noetherian scheme admits a finite
subfamily with the same residue-field lifting property. The sources may be arbitrary
schemes; no quasi-compactness or separation assumption is made on them.

Source: ILO, Travaux de Gabber, Exposé II, Corollary 2.2.4, printed p. 27
(blueprint: lem-per-prime-to-ell-decomposed-etale-finite-subcover).

Proof plan:
1. The finite affine Noetherian cover gives local Noetherianness and quasi-compactness.
   By `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal` and
   `lem-sfb-noetherian-space-compact-subsets`, the underlying space is Noetherian.
   Local Noetherianness gives quasi-separatedness by
   `lem-weil-pbc-locally-noetherian-quasi-separated`. Hence the underlying space is spectral
   by `lem-weil-pbc-qcqs-scheme-spectral`, and its constructible topology is quasi-compact by
   `lem-weil-pbc-spectral-constructible-topology-quasi-compact`.
2. For each index, take the locus of target points admitting a source point of finite
   residue degree prime to ell. Proposition 2.2.2, recorded as
   `lem-per-prime-to-ell-decomposed-locus-constructible`, says this locus is open in the
   constructible topology. This uses neither quasi-compactness nor separation of the source.
3. The lifting hypothesis says that these loci cover the target. Compactness yields a
   finite subcover, and unfolding the loci gives the required finite subset of indices.
   For the empty scheme, use the empty subset.
-/
theorem primeToEllDecomposed_etale_finite_subcover
    (X : Scheme.{u}) [IsNoetherian X] (ell : ℕ) (hEll : ell.Prime)
    {I : Type w} (U : I → Scheme.{u}) (f : ∀ i : I, U i ⟶ X)
    (hEtale : ∀ i : I, Etale (f i))
    (hCover : ∀ x : X, ∃ (i : I) (z : U i),
      f i z = x ∧ ((f i).residueFieldMap z).hom.Finite ∧
        Nat.Coprime ((f i).residueDegree z) ell) :
    ∃ I₀ : Set I, I₀.Finite ∧ ∀ x : X, ∃ (i : I) (_ : i ∈ I₀) (z : U i),
      f i z = x ∧ ((f i).residueFieldMap z).hom.Finite ∧
        Nat.Coprime ((f i).residueDegree z) ell := by
  sorry

end AlgebraicGeometry
