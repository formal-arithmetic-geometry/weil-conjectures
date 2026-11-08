/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization

public import Submission.WeilConjectures.CategoryTheory.InternalSectionTensorComparison
public import Submission.WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import Submission.WeilConjectures.CategoryTheory.RingObjects.Ab
public import Submission.WeilConjectures.CategoryTheory.Sites.MonObj
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.MapMod
public import Submission.WeilConjectures.CategoryTheory.SheafTensor
public import Submission.WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Submission.WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Submission.WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.Abelian
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Submission.WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import Submission.WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
public import Submission.WeilConjectures.CategoryTheory.InternalSectionModuleFlat
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Submission.WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import Submission.WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
import Submission.WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Adjunction.Opposites
import Submission.WeilConjectures.CategoryTheory.DerivedSectionScalarTransport
public import Submission.WeilConjectures.CategoryTheory.InternalSectionScalarAdjunction

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Scalar adjunctions under section reconstruction

Source: Stacks Project, Modules on Sites, Tags 03EK and 0GMW; Cohomology on Sites,
Tags 06YS, 06YY and 07A6; Derived Categories, Tag 09T5; blueprint main-20261015,
det-prop-scalar-six-pullback.proof.md, (1), first paragraph
(blueprint: lem-sfb-internal-section-scalar-adjunction).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
universe u c v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct ChangeOfRings
-- Upstream made these instances local (InternalSectionTensorComparison, SheafTensor).
attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory
attribute [local instance] sfbSheafTensor_monoidalPreadditive sfbSheafTensor_hasWeakSheafify
attribute [instance] SheafOfModules.ScalarDerivedPair.extension_additive

namespace CategoryTheory.InternalAbelianSheafModule

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [UnivLE.{max c v, u}] [HasSheafify J AddCommGrpCat.{u}]
  [(J.W (A := AddCommGrpCat.{u})).IsMonoidal]

variable {R S : Sheaf J AddCommGrpCat.{u}}
  [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]


variable [HasDerivedCategory.{w} (scalarInternalModules J R)]
  [HasDerivedCategory.{w} (scalarInternalModules J S)]
  [HasDerivedCategory.{w} (SheafOfModules.scalarModules J (sectionRingSheaf J R))]
  [HasDerivedCategory.{w} (SheafOfModules.scalarModules J (sectionRingSheaf J S))]

open SheafOfModules

omit [UnivLE.{max c v, u}] in
private theorem inverseMate_isIso
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    {L : A ⥤ B} {U : B ⥤ A} {F : D ⥤ E} {V : E ⥤ D}
    {G : A ⥤ D} {H : B ⥤ E} [G.IsEquivalence] [H.IsEquivalence]
    (adj : L ⊣ U) (adj' : F ⊣ V) (β : U ⋙ G ≅ H ⋙ V) :
    IsIso (((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ β.hom)).natTrans) := by
  let α := ((mateEquiv adj adj').symm (TwoSquare.mk _ _ _ _ β.hom)).natTrans
  let βop : TwoSquare H.op U.op V.op G.op := TwoSquare.mk _ _ _ _ (NatTrans.op β.hom)
  have hi := isIso_mateEquiv_of_isEquivalence adj.op adj'.op βop
  have he : (NatTrans.op α) = (mateEquiv adj.op adj'.op βop).natTrans := by
    ext X
    simp [α, βop, mateEquiv]
  have : IsIso (NatTrans.op α) := by rw [he]; exact hi
  have (X : A) : IsIso (α.app X) := by
    have hX : IsIso ((α.app X).op) :=
      NatIso.isIso_app_of_isIso (NatTrans.op α) (Opposite.op X)
    exact isIso_of_op (α.app X)
  exact NatIso.isIso_of_isIso_app α

noncomputable local instance (U : Cᵒᵖ) (N : ModuleCat ((sectionRingSheaf J S).obj.obj U)) :
    SMul (S.obj.obj U) N :=
  inferInstanceAs (SMul ((sectionRingSheaf J S).obj.obj U) N)



end CategoryTheory.InternalAbelianSheafModule
