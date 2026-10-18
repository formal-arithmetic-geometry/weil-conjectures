/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.ConstructibleTopology

/-!
# Finite completely decomposed étale subfamilies

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé II, Corollary 2.2.4,
printed p. 27, the completely decomposed case, using Proposition 2.2.3
(blueprint: lem-per-completely-decomposed-etale-finite-subcover).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory

namespace AlgebraicGeometry

/-- A completely decomposed étale covering family of a Noetherian scheme has a finite
completely decomposed subfamily. The source schemes need not be quasi-compact or separated.
Source: ILO, Travaux de Gabber, Exposé II, Corollary 2.2.4, printed p. 27, case `ell = infinity`
(blueprint: lem-per-completely-decomposed-etale-finite-subcover).

Proof:
1. The finite affine Noetherian cover makes `X` locally Noetherian (`pqf-def-locnoeth`).
   The minimal-closed-subset property
   (`lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`) gives the descending-chain
   condition. Thus every open is quasi-compact (`lem-sfb-noetherian-space-compact-subsets`).
   Local Noetherianity gives quasi-separatedness
   (`lem-weil-pbc-locally-noetherian-quasi-separated`), hence `X` is spectral
   (`lem-weil-pbc-qcqs-scheme-spectral`). Its constructible topology is quasi-compact
   (`lem-weil-pbc-spectral-constructible-topology-quasi-compact`).
2. Let `C_i` be the locus of points with a lift through `f i` inducing a residue-field
   isomorphism. Étale implies locally of finite presentation, hence locally of finite type
   (`def-weil-etale-morphism`, `def-sbc-locally-finite-presentation`,
   `def-weil-finite-type-morphism`). Through each point of `C_i`, use
   `lem-per-rational-lift-locally-closed-section` to obtain a locally closed subscheme
   on which `f i` has a section.
3. Its image lies in `C_i`: an immersion induces residue-field isomorphisms
   (`def-weil-closed-immersion`, `def-weil-open-immersion`). The residue-field maps of
   the section and `f i` compose to that isomorphism (`def-weil-residue-field`). After
   identifying the endpoints, their composite is the identity. Field homomorphisms are
   injective, so both maps are isomorphisms.
4. Each locally closed image is `O` intersected with a closed set `F`. Both `O` and the
   complement of `F` are quasi-compact opens by Step 1. The subbasis in
   `def-weil-pbc-constructible-topology` therefore makes the image open in the constructible
   topology. These images cover `C_i`, so each `C_i` is open there.
5. The hypothesis says that the `C_i` cover `X`. Constructible compactness
   (`lem-weil-pbc-spectral-constructible-topology-quasi-compact`) selects a finite subset
   of indices. Unfolding `C_i` gives the conclusion with its residue-field condition.
   If `X` is empty, the empty subset suffices. No property of the individual sources
   beyond étaleness was used. -/
theorem completelyDecomposed_etale_finite_subcover
    (X : Scheme.{u}) [IsNoetherian X] {I : Type w}
    (U : I → Scheme.{u}) (f : ∀ i : I, U i ⟶ X)
    (het : ∀ i : I, Etale (f i))
    (hcover : ∀ x : X, ∃ (i : I) (z : U i),
      f i z = x ∧ IsIso ((f i).residueFieldMap z)) :
    ∃ I₀ : Set I, I₀.Finite ∧ ∀ x : X, ∃ i ∈ I₀, ∃ z : U i,
      f i z = x ∧ IsIso ((f i).residueFieldMap z) := by
  sorry

end AlgebraicGeometry
