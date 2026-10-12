/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedQCohDirectSums
public import Sheaf.CategoryTheory.CompactObject
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.PerfectComplexRepresentatives
import Sheaf.AlgebraicGeometry.PerfectObjectCompact
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory

/-! # Small representatives of compact quasi-coherent derived objects

Source: Stacks Project, Tags 09M1 and 09IS; perfect-complex representative argument.
(blueprint: lem-sc-derived-qcoh-compact-representatives).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Compact objects of the quasi-coherent derived category have small representatives.
Source: Stacks Project, Tags 09M1 and 09IS, and the set-of-representatives argument
of `lem-pc-perfect-complexes-compact-set`.
(blueprint: lem-sc-derived-qcoh-compact-representatives).

Proof: Noetherian schemes are quasi-compact and quasi-separated. First work in
small-Hom derived models on X and on all its opens: K-injective resolutions give
these models and localization equivalences to the supplied derived category.
Compact objects are perfect by Tag 09M1: restriction to an affine open preserves
compactness since its right adjoint commutes with sums, and the affine module
criterion identifies compact objects with bounded finite-projective complexes.
Perfect complexes have a universe-u set of representatives: on affines encode
bounded finite-projective complexes by summands of finite free modules and their
matrices; glue across a finite affine cover using Mayer-Vietoris triangles and
small Hom sets. Every representative is compact by perfectObjectCompact.
Transport the representatives and their isomorphisms back along the localization
equivalence. Its additive Hom equivalences and preservation of coproducts identify
the compactness comparison maps, so compactness is preserved and reflected.
The zero object is included, including when X is empty; no nonempty indexing type
is assumed. All choices occur inside an existence theorem, not in a definition. -/
theorem derivedQCoh_compact_representatives (X : Scheme.{u}) [IsNoetherian X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    let _ : HasCoproducts.{u} (schemeDerivedQCohCategory X) := derivedQCohDirectSums X
    ∃ (S : Type u) (G : S → schemeDerivedQCohCategory X),
      (∀ s, IsCompactObject (G s)) ∧
      ∀ P : schemeDerivedQCohCategory X, IsCompactObject P →
        ∃ s, Nonempty (P ≅ G s) := by
  sorry

end AlgebraicGeometry
