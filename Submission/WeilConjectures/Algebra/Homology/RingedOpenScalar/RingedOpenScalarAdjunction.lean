/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.LocalizedModuleExactIndependent
public import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Submission.WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Submission.WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
public import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.CategoryTheory.Localization.Adjunction
import Submission.WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Scalar restriction and normalized slice extension

Source: Stacks Project, Modules on Sites, Tags 03DI, 03CY and 03DJ
(blueprint: lem-cbc-ringed-open-scalar-adjunction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe c v r w t h
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
namespace RingedOpenScalar

/-- The two unit and counit equations, with the restriction comparison displayed.
Source: Stacks 03DI (blueprint: lem-cbc-ringed-open-scalar-adjunction). -/
def Equations {A B C D : Type t} [Category.{h} A] [Category.{h} B]
    [Category.{h} C] [Category.{h} D]
    {JS : A ⥤ C} {JR : B ⥤ D} {rU : A ⥤ B} {rT : C ⥤ D}
    {qS : C ⥤ A} {qR : D ⥤ B}
    (e : JS ⋙ rT ≅ rU ⋙ JR) (d : rT ⋙ qR ≅ qS ⋙ rU)
    (adjS : JS ⊣ qS) (adjR : JR ⊣ qR) : Prop :=
  (∀ N : A, rU.map (adjS.unit.app N) ≫ d.inv.app (JS.obj N) ≫
    qR.map (e.hom.app N) = adjR.unit.app (rU.obj N)) ∧
  (∀ Q : C, e.hom.app (qS.obj Q) ≫ JR.map (d.inv.app Q) ≫
    adjR.counit.app (rT.obj Q) = rT.map (adjS.counit.app Q))

section EquationCalculus

variable {A B C D : Type t} [Category.{h} A] [Category.{h} B]
  [Category.{h} C] [Category.{h} D]
  {JS : A ⥤ C} {JR : B ⥤ D} {rU : A ⥤ B} {rT : C ⥤ D}
  {qS : C ⥤ A} {qR : D ⥤ B}
  (e : JS ⋙ rT ≅ rU ⋙ JR) (d : rT ⋙ qR ≅ qS ⋙ rU)
  (adjS : JS ⊣ qS) (adjR : JR ⊣ qR)

variable [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [JS.Additive] [JR.Additive] [rU.Additive] [rT.Additive] [qS.Additive] [qR.Additive]

variable [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
  [PreservesFiniteLimits JS] [PreservesFiniteColimits JS]
  [PreservesFiniteLimits JR] [PreservesFiniteColimits JR]
  [PreservesFiniteLimits rU] [PreservesFiniteColimits rU]
  [PreservesFiniteLimits rT] [PreservesFiniteColimits rT]
  [PreservesFiniteLimits qS] [PreservesFiniteColimits qS]
  [PreservesFiniteLimits qR] [PreservesFiniteColimits qR]

end EquationCalculus

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R S : Sheaf J CommRingCat.{max c v r}} (U : C) (a : R ⟶ S)

/-- Forget only commutativity of the given ring sheaf.
Source: Stacks 03DA (blueprint: lem-cbc-ringed-open-scalar-adjunction). -/
abbrev rings (R : Sheaf J CommRingCat.{max c v r}) :=
  (sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).obj R

/-- The recorded scalar restriction, on the original site.
Source: Stacks 03DA (blueprint: lem-cbc-ringed-open-scalar-adjunction). -/
abbrev scalars :=
  restrictScalars.{max c v r}
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map a)

/-- The same recorded scalar restriction on the localized site.
Source: Stacks 03DI (blueprint: lem-cbc-ringed-open-scalar-adjunction). -/
abbrev sliceScalars : SheafOfModules.{max c v r} ((rings.{c, v, r} S).over U) ⥤
    SheafOfModules.{max c v r} ((rings.{c, v, r} R).over U) :=
  restrictScalars ((J.overPullback RingCat.{max c v r} U).map
    ((sheafCompose J (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})).map a))

private theorem restrictScalarsExact {D : Type t} [Category.{h} D]
    {K : GrothendieckTopology D} {B E : Sheaf K RingCat.{r}}
    [HasSheafify K AddCommGrpCat.{r}] [K.WEqualsLocallyBijective AddCommGrpCat.{r}]
    (b : B ⟶ E) : PreservesFiniteLimits (restrictScalars.{r} b) ∧
      PreservesFiniteColimits (restrictScalars.{r} b) := by
  let F := restrictScalars.{r} b
  let : PreservesFiniteColimits (toSheaf.{r} B) :=
    (CategoryTheory.moduleSheaves_colimits_forgetful B).2.2.1
  let : PreservesFiniteColimits (toSheaf.{r} E) :=
    (CategoryTheory.moduleSheaves_colimits_forgetful E).2.2.1
  let : PreservesFiniteLimits (F ⋙ toSheaf.{r} B) :=
    inferInstanceAs (PreservesFiniteLimits (toSheaf.{r} E))
  let : PreservesFiniteColimits (F ⋙ toSheaf.{r} B) :=
    inferInstanceAs (PreservesFiniteColimits (toSheaf.{r} E))
  let : ReflectsFiniteColimits (toSheaf.{r} B) := inferInstance
  exact ⟨preservesFiniteLimits_of_reflects_of_preserves F (toSheaf.{r} B),
    preservesFiniteColimits_of_reflects_of_preserves F (toSheaf.{r} B)⟩

/-- Scalar restriction is exact on either site, without flatness.
Source: Stacks 03CY, 03DI (blueprint: lem-cbc-ringed-open-scalar-adjunction).
Proof: kernels are sectionwise and retain their underlying subgroup under scalar
restriction. Cokernels are abelian sheafifications of sectionwise quotients; their
module actions agree by uniqueness of extending the quotient action. Thus scalar
restriction preserves kernels and cokernels, hence finite limits and colimits.
Its additivity is the sectionwise additivity already in Mathlib. -/
theorem scalarExact :
    PreservesFiniteLimits (scalars.{c, v, r} a) ∧
    PreservesFiniteColimits (scalars.{c, v, r} a) := by
  exact restrictScalarsExact _

set_option linter.unusedSectionVars false in
/-- Scalar exactness on the slice. Source: Stacks 03CY, 03DI
(blueprint: lem-cbc-ringed-open-scalar-adjunction).
Proof: the same sectionwise kernel and sheafified cokernel argument as scalarExact,
applied on the localized site; no flatness is used. -/
theorem sliceExact :
    PreservesFiniteLimits (sliceScalars.{c, v, r} U a) ∧
    PreservesFiniteColimits (sliceScalars.{c, v, r} U a) := by
  let : PreservesFilteredColimitsOfSize.{max c v, max c v}
      (CategoryTheory.forget AddCommGrpCat.{max c v r}) :=
    preservesFilteredColimitsOfSize_shrink.{max c v, max c v r,
      max c v, max c v r} _
  let : HasSheafify (J.over U) AddCommGrpCat.{max c v r} :=
    instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover.{
      max c v r, max c v r + 1, v, max c v, max c v r} _ _
  exact restrictScalarsExact _

/-- Finite-limit component of scalar exactness. Source: Stacks 03CY, 03DI
(blueprint: lem-cbc-ringed-open-scalar-adjunction). -/
instance scalarLimits : PreservesFiniteLimits (scalars.{c, v, r} a) :=
  (scalarExact.{c, v, r} a).1
/-- Finite-colimit component of scalar exactness. Source: Stacks 03CY, 03DI
(blueprint: lem-cbc-ringed-open-scalar-adjunction). -/
instance scalarColimits : PreservesFiniteColimits (scalars.{c, v, r} a) :=
  (scalarExact.{c, v, r} a).2
/-- Finite-limit component on the slice. Source: Stacks 03CY, 03DI
(blueprint: lem-cbc-ringed-open-scalar-adjunction). -/
instance sliceLimits : PreservesFiniteLimits (sliceScalars.{c, v, r} U a) :=
  (sliceExact.{c, v, r} U a).1
/-- Finite-colimit component on the slice. Source: Stacks 03CY, 03DI
(blueprint: lem-cbc-ringed-open-scalar-adjunction). -/
instance sliceColimits : PreservesFiniteColimits (sliceScalars.{c, v, r} U a) :=
  (sliceExact.{c, v, r} U a).2

open Classical in
/-- The sheafification of an actual direct-sum generator.
Source: Stacks 03DI, 03CY (blueprint: lem-cbc-ringed-open-scalar-adjunction). -/
def generator (B : Sheaf J CommRingCat.{max c v r})
    (N : SheafOfModules.{max c v r} ((rings.{c, v, r} B).over U))
    (V : Cᵒᵖ) (phi : V.unop ⟶ U) (x : N.val.obj (op (Over.mk phi))) :
    ((localizedSystemExtension.{c, v, r} B U).obj N).val.obj V :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 (rings.{c, v, r} B).obj)).unit.app
    ((extensionByZeroPresheaf.{max c v r} (rings.{c, v, r} B) U).obj N)).app V
      (DirectSum.of (fun psi : V.unop ⟶ U ↦ N.val.obj (op (Over.mk psi))) phi x)

end RingedOpenScalar
end SheafOfModules
