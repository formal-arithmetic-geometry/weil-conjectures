module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Noetherian.Defs

import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Spectral.ConstructibleTopology

/-!
# Finite subfamilies of completely decomposed étale covers

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé II, Corollary 2.2.4,
printed p. 27, completely decomposed case `ℓ = ∞`, using Proposition 2.2.3
(blueprint: lem-per-completely-decomposed-etale-finite-subcover).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry

set_option autoImplicit false in
/-- A completely decomposed étale family over a Noetherian scheme has a finite
completely decomposed subfamily. Source: ILO, Exposé II, Corollary 2.2.4, printed p. 27,
case `ℓ = ∞` (blueprint: lem-per-completely-decomposed-etale-finite-subcover).

Proof:
1. A finite affine Noetherian cover makes `X` locally Noetherian and quasi-compact.
   The minimal-closed-subset property gives the descending-chain condition on closed
   subsets; hence every subset of `X` is quasi-compact
   (`lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`,
   `lem-sfb-noetherian-space-compact-subsets`). Locally Noetherian schemes are
   quasi-separated (`lem-weil-pbc-locally-noetherian-quasi-separated`), so `X` is spectral
   (`lem-weil-pbc-qcqs-scheme-spectral`) and its constructible topology is quasi-compact
   (`lem-weil-pbc-spectral-constructible-topology-quasi-compact`).
2. Let `C i` be the locus of points with a residue-field-isomorphism lift through `f i`.
   Étale morphisms are locally of finite presentation, hence locally of finite type
   (`def-weil-etale-morphism`, `def-sbc-locally-finite-presentation`,
   `def-weil-finite-type-morphism`). At every point of `C i`, Proposition 2.2.3 supplies
   an immersion `j : Z ⟶ X` through that point and a section `s : Z ⟶ U i` over `X`
   (`lem-per-rational-lift-locally-closed-section`).
3. The image of `j` lies in `C i`: immersions induce residue-field isomorphisms
   (`def-weil-closed-immersion`, `def-weil-open-immersion`). At any point of `Z`,
   functoriality of residue-field maps (`def-weil-residue-field`) gives field maps
   `a` and `b` whose composite `ba` is an isomorphism. Identifying its endpoints gives
   `ba = 1`; injectivity of the unital field map `b` then gives `ab = 1`, so `a` is an
   isomorphism.
4. Each locally closed image is `O ∩ F` with `O` open and `F` closed. Both `O` and the
   complement of `F` are quasi-compact by Step 1, so the constructible subbasis makes
   `O ∩ F` open (`def-weil-pbc-constructible-topology`). Steps 2--3 therefore express
   each `C i` as a union of constructible-open subsets, proving it open.
5. The hypothesis says that the `C i` cover `X`. Constructible compactness extracts
   a finite subset of indices, and unfolding `C i` gives the conclusion. If `X` is
   empty, the empty subset suffices. No quasi-compactness or separation of `U i`
   enters this argument. -/
theorem completelyDecomposed_etale_finite_subcover
    (X : Scheme.{u}) [IsNoetherian X] {I : Type w}
    (U : I → Scheme.{u}) (f : ∀ i : I, U i ⟶ X) [∀ i : I, Etale (f i)]
    (hcover : ∀ x : X, ∃ (i : I) (z : U i), f i z = x ∧ IsIso ((f i).residueFieldMap z)) :
    ∃ I₀ : Set I, I₀.Finite ∧
      ∀ x : X, ∃ (i : I) (_ : i ∈ I₀) (z : U i),
        f i z = x ∧ IsIso ((f i).residueFieldMap z) := by
  sorry

end AlgebraicGeometry
