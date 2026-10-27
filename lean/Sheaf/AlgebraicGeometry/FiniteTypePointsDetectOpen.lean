/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q33
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.Topology.LocallyClosed
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Topology.Separation.Basic
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.Topology.PresheafModuleStalkFunctor
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-! # Finite type points meet locally closed subsets and detect the whole scheme

Source: Stacks Project, Morphisms, Tags 02J1 and 02J4
(blueprint: lem-sfb-finite-type-points-detect-open).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry.Scheme

/-- Every nonempty locally closed subset of a scheme contains a finite type point,
and an open subset containing every finite type point is the whole scheme.
Finite type means locally of finite type and quasi-compact for the canonical map
from the spectrum of the residue field. No further hypothesis on the scheme is required.

Source: Stacks Project, Morphisms, Tag 02J4 (lemma-enough-finite-type-points),
with finite type points as in Tag 02J1 (definition-finite-type-point).
(blueprint: lem-sfb-finite-type-points-detect-open)

Proof plan:
1. Write the locally closed subset as G ∩ C with G open and C closed. Choose a point
   in it, then an affine open W containing that point and contained in G, using
   lem-weil-pbc-affine-opens-basis. The subset C ∩ W is nonempty and closed in W.
2. The affine scheme W is quasi-compact by lem-weil-pbc-affine-scheme-qcqs and T0
   by lem-weil-pbc-scheme-sober: equal point closures would give two generic points
   of the same irreducible closed subset. Apply lem-sc-quasi-compact-kolmogorov-closed-point
   to C ∩ W, obtaining v in it with singleton closed in W.
3. The inclusion j : W → V is an open immersion (def-weil-open-immersion).
   Restriction of germs gives inverse ring maps on the stalks at v, using
   def-weil-pbc-module-stalk and its germ-equality criterion. They identify maximal
   ideals and residue fields (def-weil-residue-field), and identify the composite
   Spec κ_W(v) → W → V with the canonical residue-field map at v in V.
4. By lem-trf-closed-point-residue-immersion, Spec κ_W(v) → W is a closed immersion.
   Its composite with j is an immersion (def-weil-closed-immersion), hence locally
   of finite type by clause (2) of lem-weil-pbc-immersion-base-change-lft.
5. Spec κ_V(v) is a singleton (def-weil-affine-spectrum). Its inverse image of each
   affine open of V is empty or a singleton, hence quasi-compact. Thus its canonical
   map to V is of finite type (def-weil-finite-type-morphism), proving the first clause.
6. If an open O containing every finite type point had nonempty complement, apply
   the first clause to that closed, hence locally closed, complement to obtain a
   finite type point outside O, a contradiction. For the empty scheme O is already univ.
-/
theorem finiteTypePoints_meet_locallyClosed_and_detect_open (V : Scheme.{u}) :
    (∀ (Z : Set V), IsLocallyClosed Z → Z.Nonempty →
      ∃ v ∈ Z, LocallyOfFiniteType (V.fromSpecResidueField v) ∧
        QuasiCompact (V.fromSpecResidueField v)) ∧
    (∀ (O : Set V), IsOpen O →
      (∀ v : V, (LocallyOfFiniteType (V.fromSpecResidueField v) ∧
        QuasiCompact (V.fromSpecResidueField v)) → v ∈ O) → O = Set.univ) := by
  sorry

end AlgebraicGeometry.Scheme
