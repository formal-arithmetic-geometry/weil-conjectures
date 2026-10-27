/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules
public import Sheaf.CategoryTheory.RingedToposMorphism
public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.CategoryTheory.RingedSiteModules
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import Sheaf.AlgebraicGeometry.AlgebraicSpaceHigherDirectImageQuasiCoherent
import Sheaf.AlgebraicGeometry.AlgebraicSpaceCoherentAbelian
import Sheaf.AlgebraicGeometry.AlgebraicSpaceClosedCoherentModules
import Sheaf.AlgebraicGeometry.SpaceAffineModuleHigherImageVanishing

/-! # Coherent higher direct images under proper algebraic-space morphisms

Source: Stacks Project, Cohomology of Algebraic Spaces, Tag 08AR,
lemma-proper-pushforward-coherent; coherence criterion Tag 07UB
(blueprint: lem-sfb-space-proper-coherent-higher-images).

Coherence on a locally Noetherian algebraic space is the existing finite-presentation
predicate on its small etale ringed site, by Tag 07UB. Ordinary higher direct images
are Mathlib's injective-resolution right derived functors of the canonical module
direct image, expressed on the equivalent small affine ringed model and transported
back. No derived-localization universe or additional resolution hypothesis is needed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- Proper higher direct images of a coherent module are coherent in every nonnegative
integer degree. Properness is separatedness, quasi-compactness, local finite type on
compatible etale scheme charts, and closedness after every algebraic-space base change.
Local Noetherianity is tested on every etale scheme chart. Properness implies that X
is locally Noetherian too. Tag 07UB identifies finite presentation here with the stated
affine-chart description by finite modules N and sections B tensor_R N.

Source: Stacks Project, Cohomology of Algebraic Spaces, Tags 08AR and 07UB
(blueprint: lem-sfb-space-proper-coherent-higher-images).

The specified small-module equivalences are restriction to actual affine etale charts.
Mathlib's rightDerived is cohomology of the direct image of an injective resolution
in ALL module sheaves, not a resolution in the subcategory of coherent modules.
Transporting along these equivalences gives precisely the higher image on Y_et.
The displayed resolution instance comes from the small ringed site's Grothendieck
property; it adds no hypothesis on f, F, X or Y. The natural number i ranges over
exactly the integers i >= 0, including degree zero.

Proof (the six steps of Tag 08AR):
1. By pqf-lem-locnoeth-lft on compatible scheme charts, X is locally Noetherian.
   Use lem-trf-space-fibre-products-etale-covers, lem-sfb-space-proper-base-change
   and lem-sfb-space-higher-image-etale-restriction to restrict to an affine
   Noetherian etale chart of Y. Coherence is chartwise by 07UB. Over this affine
   base, X is quasi-compact by properness and quasi-separated since its relative
   diagonal is closed, hence affine and quasi-compact on scheme tests by
   lem-weil-pbc-closed-immersion-integral-separated-uc. Thus X is Noetherian.
2. Let P(M) mean coherence of all nonnegative higher images. P holds for zero and
   is invariant under isomorphism. The module categories are Grothendieck and have
   enough injectives by lem-pur-ringed-site-grothendieck-abelian and
   lem-sp-grothendieck-enough-injectives. Direct image is additive and left exact,
   as the right adjoint of module tensor pullback. Apply
   lem-weil-pbc-derived-functor-long-exact to a coherent short exact sequence.
   All higher images are quasi-coherent by
   lem-sfb-space-higher-direct-image-quasi-coherent. By
   lem-sfb-space-qcoh-kernels-colimits, kernels and images stay quasi-coherent.
   If two source terms have P, each higher image of the third is an extension of
   coherent subquotients, using lem-sfb-space-noetherian-coherent-support and
   lem-sfb-space-coherent-abelian. The degree-zero sequence begins at zero.
   This proves two-out-of-three.
3. Finite sums of injective resolutions are injective resolutions, by coordinatewise
   extension across monomorphisms. Additivity of direct image and cohomology gives
   additivity of every higher image. A summand is the kernel of an idempotent
   endomorphism, so lem-sfb-space-coherent-abelian shows that P(M^r) implies P(M)
   for r >= 1.
4. For an integral reduced closed subspace i : Z -> X, the map g = i followed by f
   is proper by lem-sfb-space-closed-subspace-proper and
   lem-sfb-space-proper-composition. The node
   lem-sfb-space-chow-acyclic-full-support-witness gives a projective Chow twist
   G = pi_* L^d on Z, coherent, with full support and zero annihilator, such that
   g_* G is coherent and all its positive higher images vanish.
5. Set M = i_* G. It is coherent by lem-sfb-space-closed-coherent-modules. The
   closed immersion is affine on scheme tests by
   lem-weil-pbc-closed-immersion-integral-separated-uc, so
   lem-sfb-space-affine-module-higher-image-vanishing kills its positive module
   higher images. Apply lem-sfb-ringed-topos-relative-leray: only row zero survives,
   giving R^p f_* i_* G isomorphic to R^p g_* G. Thus P(M) holds. Let J be the
   kernel of O_X -> i_* O_Z. The quotient and essential-image assertions of
   lem-sfb-space-closed-immersion-quasi-coherent-modules identify the action on M
   through O_X/J. Since G has zero annihilator, a local function annihilates M
   exactly when its image in O_Z is zero, on the same etale charts. Therefore
   Ann(M) = J and its scheme theoretic support is exactly Z.
6. Apply lem-sfb-space-coherent-two-of-three-devissage using the zero, isomorphism,
   two-out-of-three and sum-reflection properties of steps 2 and 3, and the
   witnesses of steps 4 and 5. It gives P(F), including on the empty space since
   P(0) was checked. Step 1 descends coherence to the original Y in every degree. -/
theorem isFinitePresentation_moduleHigherDirectImage_of_proper
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hf : MapIsProper f)
    (hY : ∀ T : Y.EtaleSite, IsLocallyNoetherian (Y.etaleForget.obj T))
    (F : X.Modules) (hF : F.IsFinitePresentation) (i : ℕ) :
    (Y.smallModuleEquivalence.inverse.obj
      ((@Functor.rightDerived X.SmallModules _ Y.SmallModules _ _
        (@InjectiveResolution.instHasInjectiveResolutions X.SmallModules _ _
          (@IsGrothendieckAbelian.enoughInjectives _ _ _
            (SheafOfModules.isGrothendieckAbelian X.smallStructureRings)))
        _ (smallModuleDirectImage f) _ i).obj
          (X.smallModuleRestriction.obj F))).IsFinitePresentation := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
