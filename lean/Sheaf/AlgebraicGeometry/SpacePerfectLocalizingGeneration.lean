/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects

/-! # Perfect localizing generation for algebraic spaces

Source: Stacks Project, spaces-perfect.tex, Tags 08F3, 09IY and 09M8;
derived.tex, Tag 09SN (blueprint: lem-sfb-space-perfect-localizing-generation).

All closures are in the ambient derived category of module sheaves on the small etale
site, represented by its recorded small affine model. Coproduct indices lie in `Type u`.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- On a quasi-compact quasi-separated algebraic space, the quasi-coherent derived
subcategory is closed under ambient coproducts and is the smallest strictly full
subcategory containing perfect objects and closed under shifts, cones, retracts and
arbitrary set-indexed coproducts.
Quasi-separatedness is expressed by compactness of every fibre product of two affine
scheme charts, the absolute criterion of spaces-properties.tex,
lemma-characterize-quasi-separated, rather than the diagonal relative to S.
Source: Stacks Tags 08F3, 09IY, 09M8 and 09SN
(blueprint: lem-sfb-space-perfect-localizing-generation).

Proof in words:
1. On the small skeleton, module sheaves are Grothendieck by
   lem-pur-ringed-site-grothendieck-abelian, and have K-injective resolutions by
   lem-sfb-grothendieck-k-injective. Coproducts are filtered colimits of finite subsums;
   finite subsums are exact by the abelian biproduct identities and filtered colimits
   preserve exactness. The finite-subsum identification follows from the universal
   property: compatible maps out of finite subsums are families of maps out of summands.
   Apply lem-kun-grothendieck-derived-coproducts and
   src-weil-derived-homology-preserves-coproducts. Cohomology of the ambient sum is the
   sum of cohomologies, quasi-coherent by lem-sfb-space-qcoh-kernels-colimits. Fullness
   restricts its universal property to D_QCoh.
2. Cohomology is functorial and shifts reindex it, so D_QCoh is strictly full and
   shift-stable. By lem-sf-derived-homology-long-exact, cohomology of a cone is an
   extension of a cokernel by a kernel. Apply lem-sfb-space-qcoh-kernels-colimits and
   lem-sfb-space-qcoh-extension-closed; rotation gives two-out-of-three. Cohomology
   of a retract is the image of an idempotent, hence quasi-coherent. Perfect objects
   belong to D_QCoh by lem-sfb-space-perfect-objects-compact.
3. Choose the perfect weak generator of lem-sfb-space-perfect-weak-generator, compact
   in D_QCoh by lem-sfb-space-perfect-objects-compact. Shifted Hom vanishing gives
   the generating-family criterion after replacing n by -n. Apply
   lem-pc-compact-generators-build-objects to this singleton. Every E is the telescope
   of a sequence whose first term and successive attaching terms are sums of shifts
   of the generator. These coproducts and triangles are ambient ones by step 1.
4. Any strictly full subcategory with the stated closures contains the generator,
   its shifts and their sums. Induction using the attaching triangles puts every
   sequence term in it. It therefore contains the sum of the sequence terms and
   the cone of its endomorphism 1-shift, namely E. Thus D_QCoh is contained in every
   such subcategory. Step 2 and coproduct closure show it is itself one of them. -/
theorem perfect_localizing_generation {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules]
    [CompactSpace (Point X.obj.obj)]
    (hqs : ∀ (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj)
      (b : yoneda.obj V ⟶ X.obj.obj), IsAffine U.left → IsAffine V.left →
        CompactSpace (Point (Limits.pullback a b))) :
    HasCoproducts.{u} X.DerivedModules ∧
    (derivedQCohProperty.{u, w} X).IsClosedUnderIsomorphisms ∧
    (derivedQCohProperty.{u, w} X).IsStableUnderShift ℤ ∧
    (derivedQCohProperty.{u, w} X).IsTriangulatedClosed₃ ∧
    (derivedQCohProperty.{u, w} X).IsStableUnderRetracts ∧
    (∀ I : Type u,
      (derivedQCohProperty.{u, w} X).IsClosedUnderColimitsOfShape (Discrete I)) ∧
    (∀ E : X.DerivedModules,
      SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, 0, w}
        X.smallStructureSheaf E →
        derivedQCohProperty.{u, w} X E) ∧
    ∀ L : ObjectProperty X.DerivedModules,
      L.IsClosedUnderIsomorphisms → L.IsStableUnderShift ℤ →
      L.IsTriangulatedClosed₃ → L.IsStableUnderRetracts →
      (∀ I : Type u, L.IsClosedUnderColimitsOfShape (Discrete I)) →
      (∀ E : X.DerivedModules,
        SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, 0, w}
        X.smallStructureSheaf E → L E) →
      derivedQCohProperty.{u, w} X ≤ L := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
