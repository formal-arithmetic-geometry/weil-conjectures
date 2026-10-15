/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
public import Sheaf.Paper.ProEtaleConstructibleSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import Sheaf.CategoryTheory.RingedSiteModules
import WeilConjectures.ConstructibleSheaf.Refinement
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.AlgebraicGeometry.ProEtaleOperations
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Sheaf.Paper.ProEtaleLocallyConstantSheaf
import Sheaf.AlgebraicGeometry.ProEtaleGeometricStalk
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.ProEtaleConstantSheafStalk
import Sheaf.CategoryTheory.FiniteTypeLocallyConstantSerre
import Sheaf.Paper.CohomologyInWeakSerreSubcategory
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.AlgebraicGeometry.ProEtaleRingInverseImage
import Sheaf.Paper.ProEtaleFixedModuleLocalConstancy
import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction

/-!
# Bounded constructible pro-etale complexes form a triangulated subcategory

Source: Stacks Project, Tags 09AL, 09B5 and 06UQ; Weil blueprint,
`def-weil-finite-torsion-constructibility`
(blueprint: lem-weil-proetale-dbc-triangulated).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Bounded globally constructible cohomology is invariant under isomorphisms and
cuts out a full triangulated subcategory. Source: Stacks Project, Tags 09AL,
09B5 and 06UQ; Weil blueprint, `def-weil-finite-torsion-constructibility`
(blueprint: lem-weil-proetale-dbc-triangulated).

Proof:
1. The category of modules over the constant ring sheaf is abelian, and its derived
cohomology is `DerivedCategory.homologyFunctor`. Globally constructible sheaves
contain zero and are invariant under isomorphisms. A finite ring is Noetherian.
2. Refine two finite stratifications by pairwise intersections
(`lem-weil-pbc-constructible-stratification-intersection`). Canonical inverse image
preserves constant coefficient rings and constant module local models, commutes
with composition and localized restriction, and pulls trivializing covers back to
covers (`def-weil-proetale-inverse-image`, `def-weil-pbc-proetale-operations`,
`lem-weil-proetale-weakly-etale-localization`). Stalks of constant local models are
the modules themselves (`lem-weil-proetale-constant-sheaf-stalk`); hence the refined
local models remain finite.
3. Exact inverse image and `lem-weil-pbc-locally-constant-derived-serre` imply that
kernels, cokernels and extensions are locally constant of finite type on each
common stratum. Finite type over the finite coefficient ring gives finite stalks.
The common global finite partition therefore witnesses constructibility of these
kernels, cokernels and extensions, proving the weak Serre closure conditions.
4. Apply `lem-sbc-cohomology-in-weak-serre-subcategory` to this weak Serre class
in the module category, and intersect with the bounded derived class.
5. Boundedness is exactly finite support of nonzero cohomology in integer degrees.
Thus the intersection is precisely the displayed predicate. Strict fullness gives
isomorphism closure; the triangulated structure gives zero, all shifts and middle
vertices of distinguished triangles. Applying shifts by `n` and `-n` gives the
stated shift equivalence, including negative shifts. -/
theorem proEtale_bounded_constructible_isTriangulated
    (Y : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    ObjectProperty.IsClosedUnderIsomorphisms (fun K : proEtaleDerivedCategory Y A ↦
      Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y A)) i).obj K)} ∧
      ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf Y A
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules Y (proEtaleConstantRing Y A)) i).obj K)) ∧
    ObjectProperty.IsTriangulated (fun K : proEtaleDerivedCategory Y A ↦
      Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y A)) i).obj K)} ∧
      ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf Y A
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules Y (proEtaleConstantRing Y A)) i).obj K)) := by
  sorry

end AlgebraicGeometry.Scheme
