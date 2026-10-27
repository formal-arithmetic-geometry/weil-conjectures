/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NM
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.CategoryTheory.CompactObject

import Sheaf.AlgebraicGeometry.SpaceDerivedEtaleChartCalculus
import Sheaf.AlgebraicGeometry.AffineEtaleDerivedModuleRealization
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! # Compact quasi-coherent derived objects on algebraic spaces are perfect

Source: Stacks Project, spaces-perfect.tex, Tag 09M8,
`proposition-compact-is-perfect`, compact-to-perfect implication
(blueprint: lem-sfb-space-compact-objects-perfect).

The category is the full subcategory with quasi-coherent cohomology in the existing
small ringed model, equivalent to the original small étale module topos. Compactness
is stated in this subcategory. Its witness includes the existence of its coproducts.
Local perfectness is asserted for the underlying derived object.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A compact object of D_QCoh on a quasi-compact quasi-separated algebraic space is
perfect. Absolute quasi-separatedness is tested by the quasi-compactness of the fibre
product of every pair of affine schemes mapping to X. The coproduct witness in
`hcompact` supplies exactly the structure needed by the recorded compactness predicate.
Source: Stacks Project, spaces-perfect.tex, Tag 09M8,
`proposition-compact-is-perfect`, compact-to-perfect implication
(blueprint: lem-sfb-space-compact-objects-perfect).

Proof:
1. Choose a surjective affine étale chart j : U = Spec A → X by
   lem-sfb-qc-space-affine-etale-atlas. By lem-sfb-space-affine-source-qc-separated,
   j is quasi-compact and separated, hence quasi-separated. By
   lem-sfb-space-derived-etale-chart-calculus, restriction j* is exact and left
   adjoint to Rj*. By lem-sfb-space-derived-pushforward-coproducts, Rj* preserves
   quasi-coherent cohomology and small coproducts. The adjunction restricts to D_QCoh,
   with coproducts computed in the ambient derived categories.
2. For every small family L_i on U, adjunction identifies Hom(j*P, directSum L_i)
   with Hom(P, directSum Rj*L_i). Compactness of P identifies this with the direct
   sum of Hom(P, Rj*L_i), hence with the direct sum of Hom(j*P, L_i). Naturality
   identifies the resulting bijection with the canonical coproduct map. Thus j*P
   is compact in D_QCoh(U).
3. By lem-sfb-affine-etale-derived-module-realization, the termwise associated
   module functor gives D(A) ≃ D_QCoh(U). Choose E mapping to j*P. Equivalences
   preserve coproducts by their universal property and preserve their injection
   maps. Their fully faithful Hom bijections therefore make E compact in D(A).
4. By lem-sfb-ring-derived-compact-perfect, E has a bounded representative F with
   each term a summand of a finite free A-module. The termwise associated module
   functor takes A^n to O_U^n by its affine étale formula B tensor_A M, and takes
   each splitting relation to the same relation. It therefore takes F to a
   strictly perfect representative of j*P, with the same bounds.
5. Represent P by a K-injective complex I using prop-pur-kinjective-resolutions-exist.
   Its restriction to U remains K-injective by lem-pur-kinjective-restrict-localized.
   By lem-pur-rhom-into-kinjective-local, the derived identification from step 4
   lifts to a chain map from that strictly perfect complex to I|U. This map is a
   quasi-isomorphism since cohomology factors through localization. For any étale
   object V over X, the scheme W = V ×_X U covers V. Restrict the chain map to W;
   exact restriction preserves its quasi-isomorphism, bounds and termwise finite
   free splittings. This is the local condition of
   def-weil-pbc-strict-perfect-coefficient-package for I, so P is perfect.
   The small ringed-model equivalence preserves these module and local conditions. -/
theorem isPerfect_of_compact
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasDerivedCategory.{w} X.SmallModules]
    (hqc : CompactSpace (Point X.obj.obj))
    (hqs : ∀ (U V : Over S) (a : yoneda.obj U ⟶ X.obj.obj)
      (b : yoneda.obj V ⟶ X.obj.obj), IsAffine U.left → IsAffine V.left →
        CompactSpace (Point (Limits.pullback a b)))
    (P : X.DerivedQCoh)
    (hcompact : ∃ hcoprod : HasCoproducts.{u} X.DerivedQCoh,
      @IsCompactObject.{u} X.DerivedQCoh _ _ hcoprod P) :
    SheafOfModules.IsPerfectOnRingedSiteOfUniverses.{u, u, u, w}
      X.smallStructureSheaf P.obj := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
