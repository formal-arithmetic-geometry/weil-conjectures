/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.SiteInverseImageTensor
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import Mathlib.CategoryTheory.MorphismProperty.Limits
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineBaseChangeDense
import WeilConjectures.AlgebraicGeometry.UniversallyHomeomorphIntegral

/-! Local ingredients for topological invariance of the small pro-etale topos. -/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Topological invariance over an affine target.
Source: Stacks Project, Tag 09AB, affine part of `proetale-lemma-thickening`.
Proof: Convert the universally-homeomorphic hypothesis to the integral, universally
injective, surjective formulation. The composite of affine-basis inclusion over Y with
base change is a dense subsite over X, so its sheaf pushforward is an equivalence. The
composition comparison identifies this functor with the actual direct image followed
by restriction to the affine basis of Y. The latter restriction is itself an equivalence,
so cancellation of equivalences gives the result for the actual direct image. The argument
includes the empty affine scheme and non-finite integral universal homeomorphisms.
(blueprint: lem-trf-proetale-affine-topological-invariance) -/
theorem proEtaleSheafDirectImage_affine_topological_invariance {X Y : Scheme.{u}}
    [IsAffine Y] (r : X ⟶ Y) (hr : (topologically IsHomeomorph).universally r) :
    (proEtaleSheafDirectImage r (Type (u + 1))).IsEquivalence := by
  have := isUniversalHomeomorphism_of_universally_isHomeomorph r hr
  have := proEtaleAffineBaseChange_isDenseSubsite r
  have : ((AffineProEt.toProEt Y ⋙ proEtaleBaseChange r).sheafPushforwardContinuous
      (Type (u + 1)) (AffineProEt.topology Y) (ProEt.topology X)).IsEquivalence :=
    inferInstance
  have : (proEtaleSheafDirectImage r (Type (u + 1)) ⋙
      AffineProEt.sheafPushforward Y (Type (u + 1))).IsEquivalence := by
    exact Functor.isEquivalence_of_iso
      (Functor.sheafPushforwardContinuousComp (AffineProEt.toProEt Y)
        (proEtaleBaseChange r) (Type (u + 1)) (AffineProEt.topology Y)
        (ProEt.topology Y) (ProEt.topology X)).symm
  have : (AffineProEt.sheafPushforward Y (Type (u + 1))).IsEquivalence :=
    AffineProEt.isEquivalence_sheafPushforwardContinuous_toProEt Y
  exact Functor.isEquivalence_of_comp_right _ (AffineProEt.sheafPushforward Y (Type (u + 1)))

end AlgebraicGeometry.Scheme
