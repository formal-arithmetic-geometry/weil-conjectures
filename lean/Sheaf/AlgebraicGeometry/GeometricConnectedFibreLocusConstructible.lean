/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.Topology.Constructible
public import Sheaf.AlgebraicGeometry.GeometricComponentCountBaseChange

import Sheaf.AlgebraicGeometry.GeometricConnectedCountGenericConstancy
import Sheaf.AlgebraicGeometry.NoetherianConstructibleSubsetCriterion
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Sheaf.AlgebraicGeometry.FinitePresentationFamilyDescent

/-!
# Constructibility of geometric connected-component-count level sets

Source: Stacks Project, More on Morphisms, Tag 055I,
`lemma-nr-geom-connected-components-constructible`
(blueprint: lem-sfb-geometric-connected-fibre-locus-constructible).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For a finitely presented morphism, each finite level set of the geometric
connected-component count is locally constructible, and is constructible if the base
is Noetherian. Finite presentation is local finite presentation, quasi-compactness and
quasi-separatedness. `IsNoetherian T` means locally Noetherian and quasi-compact.
The count is evaluated over the canonical algebraic closure of the residue field;
`geometricComponentCount_baseChange` makes it independent of this choice.
`ENat.card (ConnectedComponents ...)` counts maximal nonempty connected subsets,
with zero for the empty fibre and infinity for infinitely many components.

Source: Stacks Project, More on Morphisms, Tag 055I,
`lemma-nr-geom-connected-components-constructible`, including its Noetherian proof clause
(blueprint: lem-sfb-geometric-connected-fibre-locus-constructible).

Proof:
1. Suppose T is Noetherian. Its affine Noetherian cover has a finite subcover
   (`pqf-def-locnoeth`). Finite presentation implies finite type
   (`def-sbc-locally-finite-presentation`, `def-weil-finite-type-morphism`). On every
   nonempty irreducible closed Z, `lem-sfb-geometric-connected-count-generic-constancy`
   gives a nonempty relatively open W and a constant count c. If c = m, W lies in
   the level set; otherwise W is disjoint from it. Apply
   `lem-trf-noetherian-constructible-subset-criterion` to obtain global constructibility.
2. For arbitrary T, restrict to an affine open V around the chosen point. The restricted
   morphism remains finitely presented (`lem-weil-pbc-qcqs-morphism-permanence`).
   By `lem-weil-pbc-geometric-component-count-base-change`, its level set is the
   restriction of the original level set to V.
3. By `lemma-nagata-noetherian-inverse-system-affine`, write V as the limit of the
   spectra of its finitely generated integer subalgebras. These stages are affine qcqs
   (`lem-weil-pbc-affine-scheme-qcqs`) and Noetherian
   (`lem-weil-pbc-finite-type-over-noetherian`). Apply
   `lem-weil-pbc-finite-presentation-family-descent` to the singleton family to descend
   the restricted morphism to a finitely presented morphism over one such stage.
4. Step 1 gives a constructible level set at that stage. By
   `lem-weil-pbc-geometric-component-count-base-change`, its inverse image is the level
   set on V, constructible by `lem-pur-scheme-constructible-preimage`. Step 2 identifies
   this with the original level set restricted to V. This proves local constructibility.
   All count identities and the dichotomy in step 1 include m = 0 and empty fibres.
-/
theorem isLocallyConstructible_geometricConnectedComponentCount_levelSet
    {Y T : Scheme.{u}} (f : Y ⟶ T)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] (m : ℕ) :
    Topology.IsLocallyConstructible
      {t : T | ENat.card (ConnectedComponents
        (pullback f (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t)
          (AlgebraicClosure (T.residueField t)))) ≫ T.fromSpecResidueField t) :
            Scheme.{u})) = (m : ℕ∞)} ∧
    (IsNoetherian T → Topology.IsConstructible
      {t : T | ENat.card (ConnectedComponents
        (pullback f (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t)
          (AlgebraicClosure (T.residueField t)))) ≫ T.fromSpecResidueField t) :
            Scheme.{u})) = (m : ℕ∞)}) := by
  sorry

end AlgebraicGeometry
