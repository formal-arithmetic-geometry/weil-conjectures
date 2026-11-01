/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleTowerBrownAdjunction
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.AlgebraicGeometry.FiniteCoefficientAdjoints.FiniteCoefficientAdjointComparisons
public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemDerivedComparison
public import WeilConjectures.Algebra.Homology.Coefficient.CoefficientEvaluationDerivedLeftAdjoint
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
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint

/-! # Realization of strict coefficient levels

Source: Zheng Construction 4.1 and Lemmas 4.10, 5.16, 5.22
(blueprint: def-pur-brown-tower-realization).

These are comparison data, without any existence assertion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genCtorIdx false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite SheafOfModules
namespace AlgebraicGeometry
namespace BrownTowerComparison
/-- Cache the existing pro-etale coefficient sheafification witness.
Source: Stacks 00W1 (blueprint: def-pur-brown-tower-realization). -/
instance (priority := 3000) proRingSheafify (T : Scheme.{u}) :
    HasWeakSheafify (Scheme.ProEt.topology T) CommRingCat.{u + 1} := inferInstance

/-- The coefficient quotient at the positive level `n+1`.
Source: Zheng Construction 4.1 (blueprint: def-pur-brown-tower-realization). -/
abbrev Ring (O : Type (u + 1)) [CommRing O] (t : O) (n : ℕ) :=
  O ⧸ (Ideal.span ({t} : Set O)) ^ (n + 1)

/-- The recorded strict-system category on the actual small pro-etale site.
Source: Zheng Construction 4.1 (blueprint: def-pur-brown-tower-realization). -/
abbrev ProSystem (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O] (t : O) :=
  CoefficientSystem (J := Scheme.ProEt.topology T) O t

/-- Standard localization of the strict pro-etale system category.
Source: Stacks 05RU (blueprint: def-pur-brown-tower-realization). -/
@[irreducible]
instance proSystemDerived (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O] (t : O) :
    HasDerivedCategory.{u + 2} (ProSystem T O t) := HasDerivedCategory.standard _

/-- Standard localization of each pro-etale coefficient level.
Source: Stacks 05RU (blueprint: def-pur-brown-tower-realization). -/
@[irreducible]
instance proLevelDerived (T : Scheme.{u}) (O : Type (u + 1)) [CommRing O] (t : O) (n : ℕ) :
    HasDerivedCategory.{u + 2}
      (coefficientLevelModules (J := Scheme.ProEt.topology T) O t n) :=
  HasDerivedCategory.standard _

/-- Restriction along the actual constant-ring sheafification unit. This is the
fixed-coefficient realization, retaining the original sections and maps.
Source: Stacks 03CY (blueprint: def-pur-brown-tower-realization). -/
def levelRealization {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [HasWeakSheafify J CommRingCat.{u + 1}]
    (O : Type (u + 1)) [CommRing O] (t : O) (n : ℕ) :
    coefficientLevelModules (J := J) O t n ⥤ Sheaf J (ModuleCat.{u + 1} (Ring O t n)) where
  obj M :=
    { obj :=
        { obj U := ((PresheafOfModules.restrictScalars
            (whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj
              (CommRingCat.of (Ring O t n)))) (forget₂ CommRingCat RingCat))).obj M.val).obj U
          map a := ((PresheafOfModules.restrictScalars
            (whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj
              (CommRingCat.of (Ring O t n)))) (forget₂ CommRingCat RingCat))).obj M.val).map a
          map_id := fun U ↦ by ext x; exact ConcreteCategory.congr_hom (M.val.map_id U) x
          map_comp := fun a b ↦ by
            ext x
            exact ConcreteCategory.congr_hom (M.val.map_comp a b) x }
      property := Presheaf.isSheaf_of_isSheaf_comp J _
        (forget₂ (ModuleCat.{u + 1} (Ring O t n)) AddCommGrpCat.{u + 1}) M.isSheaf }
  map a := ⟨{
    app U := ((PresheafOfModules.restrictScalars
      (whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj
        (CommRingCat.of (Ring O t n)))) (forget₂ CommRingCat RingCat))).map a.val).app U
    naturality := fun _ _ b ↦ by
      ext x
      exact ConcreteCategory.congr_hom (a.val.naturality b) x }⟩
  map_id := fun _ ↦ by ext U x; rfl
  map_comp := fun _ _ ↦ by ext U x; rfl

/-- Additivity of sectionwise realization.
Source: Stacks 03CY (blueprint: def-pur-brown-tower-realization).
Proof: scalar restriction leaves maps unchanged and therefore preserves their sums. -/
instance levelRealization_additive {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [HasWeakSheafify J CommRingCat.{u + 1}]
    (O : Type (u + 1)) [CommRing O] (t : O) (n : ℕ) :
    (levelRealization J O t n).Additive where
  map_add := by intro M N a b; ext U x; rfl

/-- The canonical localization of the sectionwise coefficient realization. Its
factorization fixes the functor on all derived morphisms, not only on cohomology.
Source: Stacks 03CY, 05RU (blueprint: def-pur-brown-tower-realization). -/
structure Realization {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [HasWeakSheafify J CommRingCat.{u + 1}]
    (O : Type (u + 1)) [CommRing O] (t : O) (n : ℕ)
    [HasDerivedCategory.{u + 2} (coefficientLevelModules (J := J) O t n)]
    [HasDerivedCategory.{u + 1} (Sheaf J (ModuleCat.{u + 1} (Ring O t n)))] where
  derived : DerivedCategory (coefficientLevelModules (J := J) O t n) ⥤
    DerivedCategory (Sheaf J (ModuleCat.{u + 1} (Ring O t n)))
  factors : DerivedCategory.Q ⋙ derived ≅
    (levelRealization J O t n).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q
  [equivalence : derived.IsEquivalence]
  bound : ∀ K a, K.IsGE a ↔ (derived.obj K).IsGE a

end BrownTowerComparison
end AlgebraicGeometry
