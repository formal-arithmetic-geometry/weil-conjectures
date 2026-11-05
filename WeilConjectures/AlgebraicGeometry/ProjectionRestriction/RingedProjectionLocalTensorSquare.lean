/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionRestrictionDataSupplement
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionLocalOrdinaryTensorSquare
import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses

/-! # Tensor coherence of the normalized localized pullback square

Source: Stacks Project, Tags 04J0 and 07A4.
(blueprint: lem-weil-pbc-ringed-projection-local-tensor-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.ProjectionRestriction

attribute [local irreducible] Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  HasDerivedCategory.standard DerivedCategory SheafOfModules.monoidalCategory

section Representatives

variable {C₀ C₁ C₂ : Type (u + 1)}
  [Category.{u} C₀] [Category.{u} C₁] [Category.{u} C₂]
  [EssentiallySmall.{u + 1} C₀] [EssentiallySmall.{u + 1} C₁]
  [EssentiallySmall.{u + 1} C₂]
  {J₀ : GrothendieckTopology C₀} {J₁ : GrothendieckTopology C₁}
  {J₂ : GrothendieckTopology C₂}
  {R₀ : Sheaf J₀ CommRingCat.{u + 1}} {R₁ : Sheaf J₁ CommRingCat.{u + 1}}
  {R₂ : Sheaf J₂ CommRingCat.{u + 1}}

@[irreducible] private def chain {L : Mod R₀ ⥤ Mod R₁} [L.Additive] {d : ExactModel L}
    {a : TensorModel R₀} {b : TensorModel R₁}
    {mu : ∀ M N, L.obj (((tensor R₀).obj M).obj N) ≅
      ((tensor R₁).obj (L.obj M)).obj (L.obj N)}
    (t : TensorComparison L d a b mu) (P Q : CochainComplex (Mod R₀) ℤ) :=
  totalMap a b L mu t.comm P Q

@[irreducible] private def twoFactors
    {F : Mod R₀ ⥤ Mod R₁} [F.Additive] {G : Mod R₁ ⥤ Mod R₂} [G.Additive]
    (d : ExactModel F) (e : ExactModel G) (P : CochainComplex (Mod R₀) ℤ) :
    e.functor.obj (d.functor.obj (DerivedCategory.Q.obj P)) ≅
      DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P)) :=
  e.functor.mapIso (d.factors.app P) ≪≫
    e.factors.app ((F.mapHomologicalComplex (.up ℤ)).obj P)

end Representatives

-- The two routes are natural transformations; resolving-pair faithfulness
-- therefore permits a componentwise representative calculation below.

end AlgebraicGeometry.Scheme.ProjectionRestriction
