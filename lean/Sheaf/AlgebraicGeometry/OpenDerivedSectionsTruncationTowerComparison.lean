/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Sheaf.Topology.OpenModuleDerivedSections
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

import Sheaf.Algebra.Homology.KInjectiveRestrictOpen
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Comparison of open derived sections and the canonical truncation tower
Source: Stacks Project, Tags 08BS and 08U1.
(blueprint: lem-sc-open-derived-sections-truncation-tower-comparison). -/

@[expose] public section
universe u wC wV wA
open CategoryTheory Opposite
set_option autoImplicit false
namespace AlgebraicGeometry

/-- Derived evaluation on an open agrees with sections after exact restriction,
including the canonical lower-truncation projection and transition maps.
Source: Stacks Project, Tag 08BS, and the uniqueness of standard truncations.
(blueprint: lem-sc-open-derived-sections-truncation-tower-comparison).

Proof: Restriction to V is exact and preserves K-injective complexes by its exact
extension-by-zero left adjoint; transport this through Modules.overEquiv V. On a
K-injective representative, both functors are termwise abelian sections on V,
so the defining derived units give a natural isomorphism on every object E.
Exact restriction is t-exact: it commutes with homology and preserves both
standard cohomological support conditions. Apply restriction to the truncation
triangle. Its vertices have the required support, hence uniqueness of truncations
gives restriction(truncGE b E) ≅ truncGE b(restriction E), respecting truncGEπ.
For b ≤ c the two resulting transition maps coincide by the universal property
of truncGE b, since their composites with its projection agree. Apply derived
sections to these isomorphisms and compose with the preceding natural comparison.
Naturality gives the two displayed squares. This works on empty opens and for
unbounded E, independently of any homology acyclicity assumption. -/
theorem openDerivedSections_truncationTower_comparison
    (X : Scheme.{u}) (V : X.Opens)
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wV} (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{wA} AddCommGrpCat.{u}]
    (E : DerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :
    let S := SheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace) (op V)
    letI : S.Additive := inferInstanceAs
      ((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
        PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj (op V)).Additive)
    let G := S ⋙ forget₂
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op V))) AddCommGrpCat.{u}
    let H := RingedSpace.openModuleSections V.toScheme.toRingedSpace ⊤
    let R := (schemeOpenRestriction X V).mapDerivedCategory
    let t := DerivedCategory.TStructure.t
      (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))
    let s := DerivedCategory.TStructure.t
      (C := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
    ∃ (e : H.rightDerivedFunctor.obj (R.obj E) ≅ G.rightDerivedFunctor.obj E)
      (en : ∀ n : ℕ, H.rightDerivedFunctor.obj ((s.truncGE (-(n : ℤ))).obj (R.obj E)) ≅
        G.rightDerivedFunctor.obj ((t.truncGE (-(n : ℤ))).obj E)),
      (∀ n : ℕ, H.rightDerivedFunctor.map ((s.truncGEπ (-(n : ℤ))).app (R.obj E)) ≫
        (en n).hom = e.hom ≫ G.rightDerivedFunctor.map ((t.truncGEπ (-(n : ℤ))).app E)) ∧
      (∀ n : ℕ, H.rightDerivedFunctor.map
        ((s.natTransTruncGEOfLE (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app (R.obj E)) ≫
          (en n).hom = (en (n + 1)).hom ≫ G.rightDerivedFunctor.map
            ((t.natTransTruncGEOfLE (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E)) := by
  sorry

end AlgebraicGeometry
