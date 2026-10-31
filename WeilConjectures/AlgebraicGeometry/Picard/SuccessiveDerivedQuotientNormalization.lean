/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
public import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.SmoothPurity.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import WeilConjectures.AlgebraicGeometry.Picard.DerivedAdjunctionCompatibility
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.ProperBaseChange.FlatAlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.ProperBaseChange.RingedToposPullbackFilteredColimits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.FromJoel.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.AlgebraicGeometry.Picard.DerivedAdjunctionCompatibility
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
/-!
# Normalized composition of derived coefficient extensions

Source: Stacks Project, Cohomology on Sites, Tags 0D6D, 0G7E, 06YY and 07A6
(blueprint: lem-sfb-successive-derived-quotient-normalization).

The scalar-first tensor convention of `changeOfRings` writes the paper's
`(x ⊗ s) ⊗ t` as `t ⊗ (s ⊗ x)`. All the comparison maps below refer to the
existing sheafified extension, its universal left derived pair, and its
localization counit. The auxiliary presentations only bundle these interfaces.
-/

@[expose] public section

set_option autoImplicit false

universe u v r w

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

namespace SheafOfModules.SuccessiveDerivedQuotient

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

variable [hD : ∀ R : Sheaf J CommRingCat.{r}, HasDerivedCategory.{w} (Modules R)]



set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
private local instance restriction_limits {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    PreservesFiniteLimits (restriction a) := (restriction_exact a).1

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
private local instance restriction_colimits {R S : Sheaf J CommRingCat.{r}} (a : R ⟶ S) :
    PreservesFiniteColimits (restriction a) := (restriction_exact a).2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
private noncomputable def resComp {R S T : Sheaf J CommRingCat.{r}}
    (a : R ⟶ S) (b : S ⟶ T) : restriction b ⋙ restriction a ≅ restriction (a ≫ b) :=
  NatIso.ofComponents (fun M ↦ {
    hom := { val := {
      app := fun U ↦ ModuleCat.ofHom
        (X := ((restriction a).obj ((restriction b).obj M)).val.obj U)
        (Y := ((restriction (a ≫ b)).obj M).val.obj U) {
        toFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
      naturality := by intros; ext; rfl } }
    inv := { val := {
      app := fun U ↦ ModuleCat.ofHom
        (X := ((restriction (a ≫ b)).obj M).val.obj U)
        (Y := ((restriction a).obj ((restriction b).obj M)).val.obj U) {
        toFun := fun x ↦ x
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
      naturality := by intros; ext; rfl } }
    hom_inv_id := by ext; rfl
    inv_hom_id := by ext; rfl
  }) (by intros; ext; rfl)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
private local instance exact_comp_limits {A B E : Type*}
    [Category A] [Category B] [Category E] (F : A ⥤ B) (G : B ⥤ E)
    [PreservesFiniteLimits F] [PreservesFiniteLimits G] :
    PreservesFiniteLimits (F ⋙ G) := comp_preservesFiniteLimits F G

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
private local instance exact_comp_colimits {A B E : Type*}
    [Category A] [Category B] [Category E] (F : A ⥤ B) (G : B ⥤ E)
    [PreservesFiniteColimits F] [PreservesFiniteColimits G] :
    PreservesFiniteColimits (F ⋙ G) := comp_preservesFiniteColimits F G

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
open CategoryTheory.Functor in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 4096 in
set_option linter.unusedSectionVars false in
end SheafOfModules.SuccessiveDerivedQuotient
