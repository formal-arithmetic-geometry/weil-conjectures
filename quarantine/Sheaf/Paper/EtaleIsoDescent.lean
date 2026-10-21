/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q126
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory
import Sheaf.AlgebraicGeometry.EtaleComparison
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.CategoryTheory.LocalizedModuleExactIndependent
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.CategoryTheory.LocalizedModuleExactForSystems

/-!
# Isomorphisms descend along étale surjections

Source: Weil conjectures blueprint, main-20261015, sec-six-functors-basics,
unit sk-prop-cohsm, lem-pur-etale-iso-descent, order 2336
(blueprint: lem-pur-etale-iso-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- Pullback along a surjective étale morphism of separated finite-type k-schemes
reflects isomorphisms between bounded constructible complexes at the fixed finite
coefficient level. The morphism is in the full constructible subcategory; pullback
is evaluated in the ambient derived category, so no preservation hypothesis is needed.

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-cohsm,
lem-pur-etale-iso-descent, order 2336 (blueprint: lem-pur-etale-iso-descent).

Proof:
1. By det-pe-morphisms-etale-comparison, the étale morphism is weakly étale.
   It is flat and locally of finite presentation, hence open by
   lem-weil-pbc-flat-lfp-open. For an affine open V of X, the images of affine opens
   of its inverse image cover V. By lem-weil-pbc-affine-scheme-qcqs a finite
   subfamily suffices. Thus u is a singleton pro-étale cover by
   def-weil-pbc-proetale-site, including the empty refinement for empty V.
2. Use lem-weil-proetale-weakly-etale-localization to identify the site of U with
   the slice site X_proet/U, preserving constant scalars. For W over U, the pair
   (W, graph(W to U)) is initial in the inverse-image indexing category: the unique
   map to (V, phi : W to U times_X V) is pr_V composed with phi. The opposite
   colimit in def-weil-proetale-inverse-image therefore evaluates to F(W).
   This is natural in W and F and fixes constant scalar sections. Consequently
   module inverse image is restriction of def-pur-localized-ringed-site, which
   is exact by lem-pur-site-restriction-module-adjunction-exact.
3. By def-weil-derived-pullback-tensor-hom, exact inverse image computes derived
   pullback termwise. By lem-weil-pbc-exact-functor-complex-cohomology its
   cohomology is the restriction of cohomology. Naturality holds on complex maps,
   their inverted quasi-isomorphisms, and composites of roofs. Thus every
   cohomology map h_r of phi restricts to an isomorphism over U.
4. For a test object T over X, base change gives a cover T times_X U of T by
   def-weil-pbc-sites-and-cohomology. Both it and its double overlap map to U.
   Injectivity of h_r on T follows from separatedness of the source sheaf.
   A target section lifts uniquely over the cover; its two overlap restrictions
   agree by injectivity there. The sheaf axiom glues the lift, whose image is the
   original section by separatedness. The inverse maps are additive, linear, and
   natural since these equations hold after applying the injective h_r. Thus
   every h_r is an isomorphism. For empty X the empty cover forces zero sections.
5. Apply lem-weil-pbc-unbounded-derived-iso-cohomology to get an ambient inverse
   of phi. The category in def-weil-finite-torsion-constructibility is full, so
   this is also an inverse in the stated bounded constructible category.
-/
theorem isIso_of_surjective_etale_pullback (P : PurityFiniteSetting.{u})
    (U X : Over (Spec (CommRingCat.of P.field.k)))
    [IsSeparated U.hom] [LocallyOfFiniteType U.hom] [QuasiCompact U.hom]
    [IsSeparated X.hom] [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
    (f : U ⟶ X) [Surjective f.left] [Etale f.left]
    (M N : (intrinsicFiniteTorsionConstructible P.coefficients.l P.extension
      P.level P.level_pos X.left).FullSubcategory)
    (φ : M ⟶ N)
    (hφ : IsIso ((@sfIntrinsicDerivedPullback P.Ring _
      (Padic.finite_coefficientExtensionRing P.coefficients.l P.extension
        P.level P.level_pos) U.left X.left f.left).map φ.hom)) :
    IsIso φ := by
  sorry

end WeilConjectures
