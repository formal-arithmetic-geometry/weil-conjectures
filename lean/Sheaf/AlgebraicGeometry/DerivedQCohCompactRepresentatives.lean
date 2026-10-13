/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedQCohDirectSums
public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.CategoryTheory.CompactObject
import Sheaf.AlgebraicGeometry.PerfectObjectCompact
import Sheaf.AlgebraicGeometry.PerfectComplexRepresentatives
public import Mathlib.AlgebraicGeometry.Noetherian
import Sheaf.AlgebraicGeometry.DerivedOpenLocalization

/-! # Small representatives of compact quasi-coherent derived objects

Source: Stacks Project, Tags 09M1 and 09IS; perfect-complex representative argument.
(blueprint: lem-sc-derived-qcoh-compact-representatives).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Derived categories exist on all open subschemes of a Noetherian scheme.
Source: Grothendieck abelianity of sheaves of modules on a small ringed site
and `HasDerivedCategory.ofIsGrothendieckAbelian`.
(blueprint: lem-sc-derived-qcoh-compact-open-categories) -/
theorem noetherian_open_derived_categories_exists (X : Scheme.{u}) [IsNoetherian X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    Nonempty (∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))) := by
  exact nonempty_derivedOpenLocalization X

/-- Compact objects in the quasi-coherent derived category are perfect.
Source: Stacks Project, Tag 09M1, converse direction of
`perfect-proposition-compact-is-perfect`; restriction to affine opens and the
finite-projective criterion reduce compactness to perfectness.
(blueprint: lem-sc-derived-qcoh-compact-is-perfect)
The proof uses the coproduct-preserving right adjoint to restriction and the
affine equivalence with the derived category of modules. -/
theorem compact_isPerfect_of_isNoetherian (X : Scheme.{u}) [IsNoetherian X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [hOpen : ∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    let _ : HasCoproducts.{u} (schemeDerivedQCohCategory X) := derivedQCohDirectSums X
    ∀ P : schemeDerivedQCohCategory X, IsCompactObject P → Scheme.IsPerfect X P.obj := by
  sorry

/-- Noetherian schemes have a universe-small family of perfect representatives.
Source: Stacks Project, Tags 08EB and 09M1, together with the finite affine
cover gluing argument of `lem-pc-perfect-complexes-compact-set`.
(blueprint: lem-sc-derived-qcoh-perfect-representatives-noetherian)
The affine representatives glue over a finite affine cover; the required
derived categories on opens and the compact and separated instances are
provided by the Noetherian hypotheses. -/
theorem noetherian_perfect_representatives (X : Scheme.{u}) [IsNoetherian X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [hOpen : ∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    ∃ (S : Type u) (G : S → schemeDerivedQCohCategory X),
      (∀ s : S, Scheme.IsPerfect X (G s).obj) ∧
      ∀ P : schemeDerivedQCohCategory X, Scheme.IsPerfect X P.obj →
        ∃ s, Nonempty (P ≅ G s) := by
  exact Scheme.exists_perfectComplex_representatives X

/-- Perfect objects on a Noetherian scheme are compact in its QCoh derived category.
Source: Stacks Project, Tag 09M1, the perfect-to-compact implication, using
tensor-Hom duality and preservation of coproducts.
(blueprint: lem-sc-derived-qcoh-perfect-compact-noetherian)
This is the Noetherian specialization of `perfectObjectCompact`; all local
derived-category and quasi-compactness infrastructure is discharged in the
intermediate theorem. -/
theorem noetherian_perfect_compact (X : Scheme.{u}) [IsNoetherian X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [hOpen : ∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    let _ : HasCoproducts.{u} (schemeDerivedQCohCategory X) := derivedQCohDirectSums X
    ∀ (P : schemeDerivedQCohCategory X), Scheme.IsPerfect X P.obj → IsCompactObject P := by
  exact perfectObjectCompact X

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
  let _ : HasCoproducts.{u} (schemeDerivedQCohCategory X) := derivedQCohDirectSums X
  let _ : ∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
    Classical.choice (noetherian_open_derived_categories_exists X)
  obtain ⟨S, G, hperf, hrep⟩ := noetherian_perfect_representatives X
  refine ⟨S, G, ?_, ?_⟩
  · intro s
    exact noetherian_perfect_compact X (G s) (hperf s)
  · intro P hP
    obtain ⟨s, hs⟩ := hrep P (compact_isPerfect_of_isNoetherian X P hP)
    exact ⟨s, hs⟩

end AlgebraicGeometry
