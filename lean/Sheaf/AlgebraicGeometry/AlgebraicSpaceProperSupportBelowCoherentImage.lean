/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q01
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleSupport
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties

import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.CategoryTheory.RightDerivedFunctorTruncationIso
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Bounded-below coherent direct image with proper supports on algebraic spaces

Source: Stacks Project, Derived Categories of Spaces, Tag 0D0R,
lemma-direct-image-coherent-bdd-below, with auxiliary base S = Y
(blueprint: lem-sfb-space-proper-support-below-coherent-image).

The categories and direct image are the existing equivalent small ringed models.
On locally Noetherian spaces, coherence is exactly local finite presentation of module
sheaves. A reduced closed subspace is specified by its closed immersion, its point range,
and reducedness of all its etale scheme charts. There is no global condition on f beyond
local finite type, and the input has no upper cohomological bound.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Direct image preserves bounded-below coherent cohomology with proper supports.
Source: Stacks Project, Tag 0D0R, lemma-direct-image-coherent-bdd-below, with S = Y
(blueprint: lem-sfb-space-proper-support-below-coherent-image).

Proof:
1. Use the small ringed models (def-weil-size-convention). Module sheaves form
   Grothendieck abelian categories (lem-pur-ringed-site-grothendieck-abelian).
2. The compatible-chart direct image (def-trf-space-etale-module-functors) is additive
   and left exact: addition and kernels are componentwise in its section limits.
   Its K-injective derived functor is the total right derived functor of
   def-sfb-right-derived-functor, transported by the specified module equivalences.
3. Choose a lower cohomology bound b for G. Negative vanishing
   (lem-weil-pbc-derived-functor-negative-vanishing) gives the same lower bound for Rf_*G.
4. For n >= b, truncate G above n using def-sbc-standard-tstructure-derived-category.
   Its cohomology is coherent and zero outside [b,n]. The surviving supports are the
   original proper supports; the other supports are empty, hence proper. Apply
   lem-sfb-space-proper-support-bounded-coherent-image (08GK) to this bounded truncation,
   with auxiliary base Y. Its direct image has coherent cohomology.
5. The map from this truncation to G is a cohomology isomorphism through n and is
   monic in degree n+1 (its source there is zero). The final clause of
   lem-weil-pbc-derived-functor-truncation-iso identifies the degree-n direct-image
   cohomology with that of G. Coherence is invariant under this isomorphism. This
   proves coherence in degrees at least b; below b the cohomology is zero by step 3.
   Thus all cohomology is coherent and a single lower vanishing bound exists. -/
theorem properSupport_below_coherent_image
    (Y : Scheme.{u}) [IsNoetherian Y] (X : AlgebraicSpace Y)
    (f : X ⟶ schemeSpace (Over.mk (𝟙 Y)))
    (hf : MapIsLocally (@LocallyOfFiniteType) f)
    [HasDerivedCategory.{w} X.SmallModules]
    [HasDerivedCategory.{w} (schemeSpace (Over.mk (𝟙 Y))).SmallModules]
    (G : X.DerivedModules)
    (hcoh : ∀ q : ℤ, (X.smallModuleEquivalence.inverse.obj
      ((DerivedCategory.homologyFunctor X.SmallModules q).obj G)).IsFinitePresentation)
    (hbelow : ∃ b : ℤ, ∀ q : ℤ, q < b →
      IsZero ((DerivedCategory.homologyFunctor X.SmallModules q).obj G))
    (hsupport : ∀ q : ℤ,
      IsClosed (moduleSupport (X.smallModuleEquivalence.inverse.obj
        ((DerivedCategory.homologyFunctor X.SmallModules q).obj G))) ∧
      ∃ (Z : AlgebraicSpace Y) (i : Z ⟶ X),
        IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) i.hom.hom ∧
        (∀ T : Z.EtaleSite, IsReduced (Z.etaleForget.obj T)) ∧
        Set.range (mapPoint i.hom.hom) =
          moduleSupport (X.smallModuleEquivalence.inverse.obj
            ((DerivedCategory.homologyFunctor X.SmallModules q).obj G)) ∧
        MapIsProper (i ≫ f)) :
    (∀ q : ℤ, ((schemeSpace (Over.mk (𝟙 Y))).smallModuleEquivalence.inverse.obj
      ((DerivedCategory.homologyFunctor (schemeSpace (Over.mk (𝟙 Y))).SmallModules q).obj
        ((derivedDirectImage f).obj G))).IsFinitePresentation) ∧
    ∃ b : ℤ, ∀ q : ℤ, q < b →
      IsZero ((DerivedCategory.homologyFunctor
        (schemeSpace (Over.mk (𝟙 Y))).SmallModules q).obj ((derivedDirectImage f).obj G)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
