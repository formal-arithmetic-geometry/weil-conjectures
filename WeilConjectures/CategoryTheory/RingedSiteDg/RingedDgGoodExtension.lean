/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Localization.Construction
public import Mathlib.CategoryTheory.Quotient
public import Mathlib.CategoryTheory.Triangulated.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import Mathlib.Topology.Sheaves.Sheaf
public import WeilConjectures.CategoryTheory.Sites.FreeModuleSheafConstruction
public import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import WeilConjectures.CategoryTheory.RingedSiteDg.RingedSiteDgModules
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import WeilConjectures.FromJoel.CategoryTheory.GradedObject.Colimits
import WeilConjectures.Algebra.Homology.Ringed.RingedDirectImagePairingLax
import WeilConjectures.CategoryTheory.RingedCocontinuousMonoidal
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.CategoryTheory.RingedSiteDg.RingedDgRestrictionDescent

/-! Derived extension from good resolutions, including its quasi-isomorphism
preservation step.

Source: Stacks sdga, Tags 0FSH, 0FSC, 0FSI and 0FTF
(blueprint: lem-sfb-ringed-dg-good-extension-derived).

Proof in words: the cone of a quasi-isomorphism between good modules is good
and acyclic.  Tensor-annihilation for good modules makes its ordinary scalar
extension acyclic, so extension sends the original map to a quasi-isomorphism.
The resolving-class and localization constructions then give the comparison,
shift and exactness data for the left derived extension.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe c v u

open CategoryTheory

namespace CategoryTheory.RingedSiteDg

variable {C : Type c} [Category.{v} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- The exact left derived extension and the postcomposition property needed for adjunction. -/
structure GoodExtensionData {O : Sheaf J CommRingCat.{u}}
    {A B : Algebra.{c, v, u} O} (φ : A ⟶ B)
    [DerivedStructure A] [DerivedStructure B]
    (ordinary : OrdinaryExtension φ) (r : RestrictionDescentData φ) where
  extension : Derived A ⥤ Derived B
  comparison : Q A ⋙ extension ⟶ ordinary.functor ⋙ Q B
  derived : extension.IsLeftDerivedFunctor comparison (quasiIsomorphisms A)
  [extensionShift : extension.CommShift ℤ]
  extensionExact : extension.IsTriangulated
  derivedPostRestriction : (extension ⋙ r.restriction).IsLeftDerivedFunctor
    ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight comparison r.restriction)
    (quasiIsomorphisms A)

end CategoryTheory.RingedSiteDg
