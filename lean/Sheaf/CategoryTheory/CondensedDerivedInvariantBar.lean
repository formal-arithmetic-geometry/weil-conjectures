/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Sheaf.CategoryTheory.CondensedEquivariantBarData
import Sheaf.CategoryTheory.CondensedProductActionInflation
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionByZeroFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Sheaf.CategoryTheory.DerivedInjectiveResolutionNaturality
import WeilConjectures.CategoryTheory.DoubleComplexTotal
import WeilConjectures.Algebra.Homology.FirstQuadrantTotalComparison
import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
import Sheaf.Algebra.Homology.ScalarInternalHomAdjunction
import Mathlib.Algebra.Homology.ModelCategory.Injective
import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel

/-! # Derived internal invariants and the profinite bar calculation

Source: main-20261015 blueprint, six-functors direct-images proof, paragraph (3),
formal internal condensed-module bar expansion
(blueprint: lem-sfb-condensed-derived-invariant-bar).
The source labels this agent-formulated input; an independent reference is still wanted.
-/

@[expose] public section
set_option autoImplicit false
universe u
namespace CategoryTheory.CondensedBar

/-- For every commutative condensed coefficient ring, the ordinary total derived invariant
functor is the finite-diagonal total of the compatible derived internal-Hom nerve.
`Assertion` includes the actual derived-object isomorphisms, augmentation normalization,
all maps of resolutions, and scalar restriction with termwise evaluation normalization.
Source: blueprint, direct-images proof, paragraph (3), formal internal bar input
(blueprint: lem-sfb-condensed-derived-invariant-bar).

Proof:
1. Use lem-sfb-condensed-product-action-inflation with trivial second group to give the
   action category its Grothendieck abelian structure. Trivial inflation is exact and
   its normalized right adjoint is invariants. Use lem-sp-grothendieck-enough-injectives
   and def-sp-injective-resolutions for nonnegative equivariant injective resolutions.
2. Free A[S] is the sheafification of the representable free module, hence extension
   by zero of the unit on the slice and flat by lem-pc-sites-modules-j-shriek-flat.
   The exact induction A[G] tensor - is left adjoint to forgetting the action. Thus
   forgetting carries equivariant injectives to ordinary internal module injectives.
3. Use lem-sfb-condensed-internal-bar-resolution. After tensoring by A[S], its augmented
   homogeneous resolution is exact. Applying equivariant Hom into an injective is exact
   on sections at every S. The augmentation object is the invariant subsheaf.
4. An equivariant homogeneous map is determined on [1] tensor [g1,...,gp]. Equivariance
   reconstructs it by g0 times that value. The closed adjunction identifies this with
   internal Hom from A[G^p]. Deleting homogeneous coordinates gives the specified first
   action face, adjacent-multiplication faces, last deletion, and unit-insertion
   degeneracies. In degree zero the differential is m maps to (g maps to gm-m).
5. Apply these functors to ONE equivariant injective resolution I. Its underlying
   resolution is injective by step 2, so lem-sp-derived-injective-resolution-naturality
   identifies every column with the ordinary second-variable derived internal Hom.
   Equivariance makes the two differentials commute. Use def-sp-double-complex-total
   for the finite-diagonal total with differential d_bar + (-1)^p d_resolution.
6. Step 3 says every augmented row is exact. Apply
   lem-sc-first-quadrant-total-column-comparison after exchanging the indices. The
   exchange of total conventions multiplies bidegree (p,q) by (-1)^(pq). The augmentation
   Gamma(I) to Tot is a quasi-isomorphism, and its localization gives the displayed
   derived-object isomorphism normalized by the invariant inclusion in degree zero.
7. Lift maps to resolutions by lem-weil-pbc-injective-resolution-lift-exists. Naturality
   holds on the entire double complex and its augmentation. Any two lifts are homotopic
   by lem-weil-pbc-lift-to-injective-unique-up-to-homotopy; multiply the vertical homotopy
   in column p by (-1)^p to totalize it. This proves independence of resolution and lift.
8. Flat A[S] in degree zero is K-flat (def-pc-kflat-complex). The free adjunction gives
   A' tensor A[S] = A'[S]. Apply lem-pur-derived-change-of-rings and
   lem-sfb-dc-hom-scalar-adjunction. The evaluation-normalized derived internal-Hom
   comparison respects all parameter maps and the action, thus every nerve map.
9. An A'-injective resolution J need not restrict to an A-injective resolution. Use
   lem-weil-pbc-lift-along-injective-quasi-iso to extend the augmentation to a map beta
   from Res J to an A-injective resolution I. The evaluation-normalized comparison of
   step 8 identifies the canonical column maps with quasi-isomorphisms. The first-
   quadrant comparison makes the total map a quasi-isomorphism. Invariants give the
   same augmentation square, whose localized inverse is exactly scalar restriction.
   Step 7 then handles every map N to Res N' and proves independence of beta.
-/
theorem condensed_derived_invariant_bar (G : Type u) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    Assertion G := by
  sorry

end CategoryTheory.CondensedBar
