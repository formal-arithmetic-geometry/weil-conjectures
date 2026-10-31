/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpaceAffineGlobalSections
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Functor.OfSequence
import WeilConjectures.AlgebraicGeometry.SpaceAffineDerivedProjectionFormula
import WeilConjectures.CategoryTheory.RingedSitePerfectDuality
import WeilConjectures.AlgebraicGeometry.SpacePerfectLocalizingGeneration
import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-! # Pullback and inverse limits on flat proper algebraic spaces

Source: Stacks Project, spaces-perfect.tex, Tag 0D3F, lemma-pullback-and-limits,
including the universal derived-Hom formulation in its proof
(blueprint: lem-sfb-proper-flat-space-pullback-limit).

The scalar pullback is the existing sheafification of O(U) tensor_A M. The comparison
is the canonical map from a functor applied to a limit to the limit of its diagram.
The natural-number index n denotes the paper's index n + 1.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- The comparison O_X tensor_A lim M_n to lim (O_X tensor_A M_n).
It is defined by the cone whose n-th leg is pullback of the module-limit projection,
using the existing scalar pullback with its specified structural A-action.
Source: Stacks Project, Tag 0D3F, lemma-pullback-and-limits
(blueprint: lem-sfb-proper-flat-space-pullback-limit). -/
def properFlatSpacePullbackLimitMap {S : Scheme.{u}} (A : Type u) [CommRing A]
    (Y : Over S) (e : Y.left ≅ Spec (.of A))
    (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y)
    {M : ℕ → ModuleCat.{u} A} (r : ∀ n : ℕ, M (n + 1) ⟶ M n) :
    (affineScalarPullback A Y e X f).obj (limit (Functor.ofOpSequence r)) ⟶
      limit (Functor.ofOpSequence r ⋙ affineScalarPullback A Y e X f) :=
  limit.post (Functor.ofOpSequence r) (affineScalarPullback A Y e X f)

/-- Pullback of a surjective module tower commutes with its limit when tested by any
complex with quasi-coherent cohomology, in the ambient module derived category.
No quasi-coherence is asserted for the limit of the pulled-back module sheaves.
Source: Stacks Project, Tag 0D3F, lemma-pullback-and-limits, first paragraph of proof
(blueprint: lem-sfb-proper-flat-space-pullback-limit).

Proof in words:
1. Put F_n = O_X tensor_A M_n. The flat affine-base projection formula
   (lem-sfb-space-affine-derived-projection-formula) makes these quasi-coherent,
   with surjective transitions. The surjective quasi-coherent tower lemma
   (lem-sfb-space-surjective-qcoh-limit) identifies (lim F_n)[0] with Rlim F_n[0]
   in the ambient module derived category.
2. For perfect E, ringed-site perfect duality (lem-sfb-ringed-site-perfect-duality)
   identifies RHom(E,N) with E-dual tensor^L N. The dual is perfect; perfect
   localizing generation puts it in D_QCoh. Its derived sections C are perfect
   over A by lem-sfb-flat-proper-space-perfect-sections. The affine projection
   formula identifies RHom(E,F_n[0]) with C tensor^L M_n[0], and similarly at lim M_n.
3. Global derived Hom commutes with the resolution-derived limit by
   lem-sfb-ringed-site-global-rhom-derived-limits. Naturality of duality and the
   projection formula identifies the map induced by our cone with the canonical
   perfect tensor-limit comparison of lem-sfb-perfect-tensor-surjective-module-limit.
   This is invertible. Taking degree-zero cohomology gives the Hom bijection for E.
4. Take the cone Q of the displayed comparison. The preceding argument for all
   shifts of E and Hom exactness (lem-weil-pbc-hom-into-triangle-exact) give
   Hom(E,Q[r]) = 0 for all perfect E and all integers r. The class of K in D_QCoh
   satisfying this vanishing is closed under shifts, cones, retracts and arbitrary
   coproducts: use the long exact Hom sequence and the coproduct universal property.
   By lem-sfb-space-perfect-localizing-generation it contains every K in D_QCoh.
   The Hom exact sequence for Q[-1], F[0], G[0], Q gives injectivity and surjectivity.
   Properness supplies quasi-compactness and separatedness, hence the required
   quasi-separatedness over the affine base. -/
theorem proper_flat_space_pullback_limit {S : Scheme.{u}} (A : Type u) [CommRing A]
    (Y : Over S) (e : Y.left ≅ Spec (.of A))
    (X : AlgebraicSpace S) (f : X ⟶ schemeSpace Y)
    (hflat : MapIsFlat f) (hproper : MapIsProper f)
    (hfp : MapIsLocallyOfFinitePresentation f ∧ MapIsQuasiCompact f.hom.hom ∧
      MapIsQuasiCompact (pullback.diagonal f.hom.hom))
    (M : ℕ → ModuleCat.{u} A) (r : ∀ n : ℕ, M (n + 1) ⟶ M n)
    (hsurj : ∀ n : ℕ, Function.Surjective (r n))
    [HasDerivedCategory.{w} X.SmallModules] (K : X.DerivedQCoh) :
    Function.Bijective
      (fun (g : K.obj ⟶ (DerivedCategory.singleFunctor X.SmallModules 0).obj
          ((affineScalarPullback A Y e X f).obj (limit (Functor.ofOpSequence r)))) ↦
        g ≫ (DerivedCategory.singleFunctor X.SmallModules 0).map
          (properFlatSpacePullbackLimitMap A Y e X f r)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
