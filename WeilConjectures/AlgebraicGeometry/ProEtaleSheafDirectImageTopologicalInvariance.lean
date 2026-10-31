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
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafAffineTopologicalInvariance
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafEquivalenceZariskiLocal

/-! Direct-image part of pro-etale topological invariance.

Source: Stacks Project, Tag 09AB, `proetale-lemma-thickening` (blueprint:
lem-trf-proetale-topological-invariance).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The direct image on set sheaves is an equivalence under a universal homeomorphism.
This is the direct-image clause of Tag 09AB; once established, the adjunction in
`ProEtaleSheafTopologicalInvariance` formally supplies the inverse-image clause and
invertibility of its unit and counit.
Source: Stacks Project, Tag 09AB, `proetale-lemma-thickening`.
Proof: Restrict to the standard affine open cover of Y. Each pullback of r is still
universally homeomorphic, so affine topological invariance applies. The open-cover
locality theorem then gives equivalence of the global direct image.
(blueprint: lem-trf-proetale-topological-invariance-direct-image)
-/
theorem proEtaleSheafDirectImage_topological_invariance {X Y : Scheme.{u}} (r : X ⟶ Y)
    (hr : (topologically IsHomeomorph).universally r) :
    (proEtaleSheafDirectImage r (Type (u + 1))).IsEquivalence := by
  apply proEtaleSheafDirectImage_isEquivalence_of_openCover r Y.affineCover
  intro i
  apply proEtaleSheafDirectImage_affine_topological_invariance
  exact (topologically IsHomeomorph).universally.pullback_snd r (Y.affineCover.f i) hr

end AlgebraicGeometry.Scheme
