/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q144
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.CategoryTheory.CompactObject

import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus
import Sheaf.CategoryTheory.RingedSitePerfectDuality
import Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel
import Sheaf.Algebra.Homology.RingedDerivedClosedSymmetricMonoidal
import Sheaf.Algebra.Homology.RingedSliceNormalizedComparisons
import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.Algebra.Homology.HomologySequence

/-! # Perfect objects are compact in the quasi-coherent derived category of a space

Source: Stacks Project, Derived Categories of Spaces, Tag 09M8,
`proposition-compact-is-perfect`, perfect-to-compact direction, and `section-spell-out`
(blueprint: lem-sfb-space-perfect-objects-compact).

The ambient derived category is formed on the recorded small affine etale ringed model,
which is equivalent to the original module topos in the original section universe.
Cohomology is tested after transport back by that equivalence. Perfection is the existing
local bounded finite-free-retract condition, with bounds allowed to vary with the chart.
Coproduct existence is concluded for D_QCoh in indexing universe u. Compactness refers
precisely to this full subcategory and its coproducts.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A perfect ambient object has quasi-coherent cohomology and is compact in D_QCoh.
Source: Stacks Project, Derived Categories of Spaces, Tag 09M8,
`proposition-compact-is-perfect`, first paragraph; `section-spell-out`
(blueprint: lem-sfb-space-perfect-objects-compact).

Proof:
1. Module sheaves are Grothendieck abelian by lem-pur-ringed-site-grothendieck-abelian,
   and admit K-injective resolutions by lem-sfb-grothendieck-k-injective. Coproducts
   are exact, as filtered colimits of finite biproducts. By
   lem-kun-grothendieck-derived-coproducts and src-weil-derived-homology-preserves-coproducts,
   termwise sums give derived coproducts and cohomology commutes with them. Closure
   under sums in lem-sfb-space-qcoh-kernels-colimits restricts these coproducts to
   the full subcategory D_QCoh, with the same injections.
2. On each etale chart a perfect representative is bounded with terms retracts of
   finite free modules, by def-weil-pbc-strict-perfect-coefficient-package. Free terms
   are quasi-coherent by def-trf-space-quasi-coherent-module; retracts, kernels and
   cokernels are quasi-coherent by lem-sfb-space-qcoh-kernels-colimits. Thus each
   cohomology sheaf is quasi-coherent on the chart. Exact restriction and local
   detection in lem-sfb-space-derived-etale-chart-calculus give the global assertion.
   This requires no bound uniform over all charts.
3. By lem-sfb-ringed-site-perfect-duality the dual P-dual is perfect, and tensoring
   with it computes RHom(P,-). The closed tensor-Hom adjunction from
   lem-sf-ringed-derived-closed-symmetric-monoidal and
   lem-sfb-derived-internal-hom-sections-model identify Hom(P,M) naturally with
   H^0(X,P-dual tensor^L M).
4. This tensor preserves quasi-coherent cohomology. Restrict to a chart carrying a
   bounded finite-free-retract representative F of P-dual. By
   lem-weil-pbc-ringed-slice-normalized-comparisons restriction is monoidal. A term
   of F has exact tensor functor, a retract of a finite power of the identity, so
   its tensor with any M has quasi-coherent cohomology. F is K-flat by
   lem-weil-pbc-independent-bounded-flat-kflat. Filter the total tensor by the
   finitely many columns of F. By lem-weil-pbc-complex-ses-homology-long-exact each
   successive middle cohomology is an extension of a cokernel by a kernel.
   Apply lem-sfb-space-qcoh-kernels-colimits and lem-sfb-space-qcoh-extension-closed,
   starting at the zero tail. Local detection gives the assertion for unbounded M.
5. The closed adjunction and symmetry make tensoring with P-dual a left adjoint.
   It therefore takes the ambient coproduct cofan of the E_i to a coproduct cofan.
   Step 4 places every resulting object in D_QCoh.
6. Apply lem-sfb-space-zeroth-hypercohomology-coproducts to this cofan. The resulting
   bijection is the canonical Hom-coproduct map: naturality of step 3 sends a map
   P to E_i to its composite with the ith coprojection. Fullness and step 1 identify
   this with the map defining IsCompactObject in D_QCoh. The empty coproduct and
   zero object are included. Restriction to the small affine model preserves all
   these constructions and the local finite-free-retract condition. -/
theorem perfectObjects_compact
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules]
    (hqc : CompactSpace (Point X.obj.obj)) (hqs : IsAbsolutelyQuasiSeparated X)
    (P : X.DerivedModules)
    (hperfect : SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
      X.smallStructureSheaf P) :
    ∃ (hP : X.derivedQCohProperty P) (hcoprod : HasCoproducts.{u} X.DerivedQCoh),
      @IsCompactObject.{u} X.DerivedQCoh _ _ hcoprod ⟨P, hP⟩ := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
