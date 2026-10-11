/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
public import Sheaf.AlgebraicGeometry.FiberDegreeBound

/-!
# Universally bounded fibres from a quasi-compact source

Source: Stacks Project, Morphisms, Lemma Tag 03JA and Definition Tag 03J4
(blueprint: lem-weil-pbc-lqf-qc-source-bounded-fibres).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

/-- A locally quasi-finite morphism whose source is quasi-compact has a single nonnegative
bound on the degrees of all its finite scheme-theoretic fibres.
Source: Stacks Project, Morphisms, Lemma Tag 03JA and Definition Tag 03J4
(blueprint: lem-weil-pbc-lqf-qc-source-bounded-fibres).

Proof outline, following the six steps of the node:
1. Choose a finite affine open cover `Uᵢ` of `X` and affine opens `Vᵢ` of `Y` with
   `f(Uᵢ) ⊆ Vᵢ`, using quasi-compactness and `lem-weil-pbc-affine-opens-basis`.
2. Each restriction `Uᵢ → Vᵢ` is locally quasi-finite by
   `lem-weil-pbc-lqf-restriction-to-opens`. It is affine, hence quasi-compact by
   `lem-weil-pbc-affine-morphism-permanence`, and therefore quasi-finite by
   `pqf-lem-qf-locqf-qc`.
3. For a finite affine morphism `Spec B → Spec A`, choose finitely many module generators
   of `B`. Tensor the resulting surjection with each residue field. Right exactness and
   `lem-weil-pbc-fibre-product-affine-spectra`, together with
   `lem-weil-pbc-spec-residue-field-identification`, bound the dimension of each fibre's
   global sections by the number of generators.
4. Factor each quasi-finite affine restriction as an open immersion into a finite affine
   scheme over `Vᵢ`, by `lem-weil-pbc-quasi-finite-affine-open-in-finite`. Use
   `lem-weil-pbc-immersion-fibre-degree-one` and
   `lem-weil-pbc-composition-fibre-degree-bound` to obtain a bound `nᵢ` for the restriction.
5. Pull the open cover back to each fibre. By
   `lem-weil-pbc-open-preimage-fibre-product`, `lem-weil-pbc-cartesian-square-pasting`, and
   `lem-weil-pbc-residue-field-point-naturality`, these opens are empty when `y ∉ Vᵢ` and
   are the fibres of `Uᵢ → Vᵢ` otherwise.
6. Apply `lem-weil-pbc-finite-open-cover-degree-sum` to conclude finiteness of each fibre
   and the bound `∑ nᵢ`. By `lem-weil-pbc-finite-over-field-affine-finite-dim`, its global
   sections form a finite-dimensional residue-field algebra giving its affine spectrum.
   Thus the sum witnesses `HasUniversallyBoundedFibers` as defined in
   `def-weil-pbc-fibre-degree-bound`. -/
theorem hasUniversallyBoundedFibers_of_isLocallyQuasiFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X]
    (hf : IsLocallyQuasiFinite f) : HasUniversallyBoundedFibers f := by
  sorry

end AlgebraicGeometry.Scheme.Hom
