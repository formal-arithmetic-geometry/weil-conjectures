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
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
public import Mathlib.CategoryTheory.Limits.Preserves.Limits

/-! # Preservation of the cyclotomic inverse limit

Source: the Roots of unity and Integral twist paragraphs of the Cartesian twists proof.
(blueprint: lem-pur-root-tower-preservation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Inverse image preserves the particular root tower defining Z_ell(1).
It need not preserve arbitrary inverse limits.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-an/
sk-prop-sfb-cartesian-coefficients-twists.proof.md, Roots of unity and Integral twist;
Stacks Project, Tags 09A5 and 03CF.
(blueprint: lem-pur-root-tower-preservation).

Proof: take the pro-etale cover carrying compatible primitive roots. On each
member the finite root modules have compatible bases over the finite constant
rings Z/ell^(n+1). Restriction to slices preserves their sectionwise inverse
limits. Use weakly etale localization to identify these slices with the small
pro-etale sites of the covering schemes. The normalized slice inverse-image
comparison transports the bases. Under the induced limit bases the module limit
comparison is the base coefficient limit comparison, which is invertible by
lem-pur-base-completion-pullback-iso. Apply
lem-pur-inverse-image-compatible-free-tower on small site models. Since these
models enlarge the Hom universe, first raise all sheaf values by ULift into the
next universe. Lifted sheafification and inverse image have their canonical
unit-normalized comparisons; their fully faithful lift preserves the relevant
limits and reflects isomorphisms. Transport back to the original sites and value
universe. Forgetting scalars and then sets preserves limits
and reflects isomorphisms. The base-changed covering covers X, so the comparison
is invertible globally. The limit-comparison criterion gives the displayed
PreservesLimit assertion. The empty-site case follows from the same covering
criterion and does not require choosing a primitive global root. -/
theorem pur_root_tower_preservation
    {X Y : Scheme.{u}} (h : X ⟶ Y) (l : ℕ) [Fact l.Prime]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    PreservesLimit (proEtaleRootsOfUnityTower Y l (Fact.out : l.Prime))
      (proEtaleSheafInverseImage h AddCommGrpCat.{u + 1}) := by
  sorry

end AlgebraicGeometry.Scheme
