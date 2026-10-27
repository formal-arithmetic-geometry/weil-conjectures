/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q19
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian

/-! # Noetherianity and coherence over a field

Source: Stacks Project, Cohomology of Schemes, Tag 01XZ,
`lemma-coherent-Noetherian`, final sentence; Morphisms, Tag 01T6,
`lemma-finite-type-noetherian`
(blueprint: lem-trf-proper-field-invertible-coherent).
-/

@[expose] public section
set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- On a proper scheme over a field, the scheme is locally Noetherian and quasi-compact,
and every invertible module, as well as the structure sheaf, is coherent.
Source: Stacks Project, Tags 01XZ and 01T6
(blueprint: lem-trf-proper-field-invertible-coherent).

Proof:
1. Every ideal of the field is zero or the whole ring, hence finitely generated
   (`def-weil-field`, `def-weil-pbc-noetherian-ring`). Thus its affine spectrum is locally
   Noetherian (`def-weil-affine-spectrum`, `pqf-def-locnoeth`).
2. Properness supplies separatedness and finite type (`def-weil-proper-morphism`,
   `def-weil-finite-type-morphism`). Apply `pqf-lem-locnoeth-lft` to the structure map for
   local Noetherianity and `lem-weil-pbc-qcqs-over-affine` for quasi-compactness.
3. Local rank-one frames (`def-sc-invertible-module`) make the invertible module
   quasi-coherent of finite type (`pqf-def-coherent`). The structure module has one
   generator. On an affine chart its map to the associated module of the ring is
   s ↦ s · τ(1), using `lem-weil-pbc-spec-module-tilde-sections`. On each basic open this
   map is the identity on the localization, hence an isomorphism on stalks and of sheaves.
   Thus the structure module is also quasi-coherent of finite type.
4. Apply `pqf-lem-coherent-ft-locnoeth` to both modules. No dimension, reducedness,
   connectedness or nonemptiness hypothesis is used.
-/
theorem proper_field_invertible_coherent
    (k : Type u) [Field k] (Y : Scheme.{u})
    (f : Y ⟶ Spec (CommRingCat.of k)) [IsProper f]
    (N : Y.Modules) [N.IsInvertible] :
    IsLocallyNoetherian Y ∧ CompactSpace Y ∧
      RingedSpace.IsCoherent Y.toRingedSpace N ∧
      RingedSpace.IsCoherent Y.toRingedSpace (SheafOfModules.unit Y.ringCatSheaf) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
