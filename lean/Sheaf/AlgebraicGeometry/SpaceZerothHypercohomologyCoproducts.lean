/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceAbsoluteQuasiSeparated
public import Sheaf.AlgebraicGeometry.SpaceChangeBase
public import Sheaf.Algebra.Homology.RingedSiteZerothHypercohomologyOfUniverses
public import Mathlib.Algebra.DirectSum.Basic

import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.ModuleCat.AB
import Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit
import WeilConjectures.CategoryTheory.DerivedCategory.HomologyCoproducts
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.AlgebraicGeometry.Scheme
import Sheaf.AlgebraicGeometry.SpaceCotangentRingMap
import Sheaf.CategoryTheory.ModuleAbelianEvaluationComparison
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.TruncationHypercohomology
import WeilConjectures.CategoryTheory.BoundedBelowCoproductFiltration
import WeilConjectures.CategoryTheory.FiniteFiltrationInductionExtension
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! # Zeroth hypercohomology and coproducts on qcqs algebraic spaces

Source: Stacks Project, Derived Categories of Spaces, Tag 08FB and the first
paragraph of the proof of Tag 09M8
(blueprint: lem-sfb-space-zeroth-hypercohomology-coproducts).

The existing small affine ringed model represents the original small étale module
category without enlarging its section universe. Coproducts are specified cofans
in the ambient unbounded derived category, not coproducts in a smaller category.
-/

@[expose] public section

set_option autoImplicit false

universe u w v

open CategoryTheory CategoryTheory.Limits DirectSum

namespace AlgebraicGeometry.AlgebraicSpace

open Classical in
/-- Zeroth hypercohomology preserves arbitrary quasi-coherent coproducts on a qcqs space.
Source: Stacks Project, Tag 08FB and the first paragraph of the proof of Tag 09M8
(blueprint: lem-sfb-space-zeroth-hypercohomology-coproducts).

Proof:
1. Module sheaves form a Grothendieck abelian category and admit K-injective resolutions
   (prop-pur-kinjective-resolutions-exist). Ambient sums are represented by termwise sums
   (lem-kun-grothendieck-derived-coproducts). Cohomology preserves these sums
   (src-weil-derived-homology-preserves-coproducts), and quasi-coherence is closed under
   sums, kernels and cokernels (lem-sfb-space-qcoh-kernels-colimits). Good truncations
   therefore commute with sums. Global sections Hom(O_X,-) are additive, left exact and
   product preserving. These claims transfer along the specified small-model equivalence.
2. Apply lem-sfb-space-change-base-to-integers to regard X as a space over Spec Z without
   changing its small ringed site. Compactness and the absolute diagonal hypothesis give
   the qcqs structure morphism by lem-sfb-space-qcqs-permanence. Specialize
   lem-sfb-space-affine-chart-uniform-qcoh-vanishing to the affine target Spec Z to obtain
   N >= 1 with R^p Gamma(M) = 0 for all quasi-coherent M and p >= N. The enlarged-site
   equivalence identifies evaluation at its terminal object with global sections.
3. Use lem-trf-space-enlarged-etale-ringed-site-model,
   lem-weil-pbc-ringed-site-module-abelian-evaluation-comparison and
   lem-weil-pbc-module-sheaves-colimits-forgetful to transfer the abelian cohomology
   colimit theorem lem-sfb-space-cohomology-filtered-colimit to module sheaves. Express
   a sum as the filtered colimit of finite subsums. Additivity identifies the finite
   comparisons, so each R^p Gamma preserves sums with the prescribed coprojections.
4. For a family with a common lower bound, thm-sp-truncation-e2 identifies the E2 terms
   with R^p Gamma of the cohomology sheaves. Step 3 makes their sum comparisons invertible.
   Apply lem-pc-bounded-below-coproduct-filtration in degree zero, then
   lem-sp-finite-filtration-induction to obtain bijectivity for this family.
5. For arbitrary K with quasi-coherent cohomology apply
   lem-sfb-space-product-preserving-derived-functor-upper-bound to tau_le(-N-1) K.
   Its derived sections vanish in degrees zero and one. The truncation triangle and
   lem-sf-derived-homology-long-exact identify H^0(X,K) with H^0(X,tau_ge(-N) K),
   naturally in K, without a lower bound on K.
6. Apply step 5 to every E_i and the given coproduct. Step 1 identifies the truncation
   of this coproduct with the coproduct of the truncated family. Step 4 applies with
   common lower bound -N. Naturality gives a commuting comparison square whose vertical
   maps and bottom map are bijective, hence the original comparison is bijective.
   Its restriction to summand i is precisely H^0(X,c.inj i). For the empty family the
   cofan is initial and additive H^0 R Gamma takes its vertex to the zero group. -/
theorem zerothHypercohomology_coproduct_bijective
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules]
    (hqc : CompactSpace (Point X.obj.obj)) (hqs : X.IsAbsolutelyQuasiSeparated)
    (I : Type v) (E : I → X.DerivedModules)
    (hE : ∀ i : I, X.derivedQCohProperty (E i))
    (c : Cofan E) (hc : IsColimit c) :
    Function.Bijective (DirectSum.toAddMonoid (fun i : I ↦
      ((ringedSiteZerothHypercohomologyOfUniverses.{u, u, u, w}
        X.smallEtaleModelTopology X.smallStructureSheaf).map (c.inj i)).hom)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
