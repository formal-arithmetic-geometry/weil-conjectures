/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Homology.DerivedInternalHomOfUniverses
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Generator.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import WeilConjectures.Algebra.Homology.HomComplexSectionsQuasiIsoOfUniverses
public import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimitSupplement
public import Mathlib.Algebra.Category.Grp.Abelian
public import WeilConjectures.Algebra.Homology.HomComplexSectionsDerivedNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
public import WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalizedOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunctionOfUniverses
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionExtensionExistsOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import WeilConjectures.Algebra.Homology.HomComplexSectionsHomotopyNaturalityOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCanonicalComparisonOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsOfUniverses
public import WeilConjectures.Algebra.Homology.HomComplexSectionsCochainsCommOfUniverses
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Category.Grp.EpiMono
public import WeilConjectures.Algebra.Homology.LocalizedModuleRestrictionQuasiIsoOfUniverses
public import Mathlib.Algebra.Homology.QuasiIso
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import WeilConjectures.Algebra.Homology.QuasiIsoOfSectionsOfUniverses
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalComplex
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficientPullbackUniverses
public import WeilConjectures.AlgebraicGeometry.ProEtaleRingInverseImage
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficientsSupplement
public import WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import WeilConjectures.CategoryTheory.RingedIdealGenerators
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import WeilConjectures.CategoryTheory.RingedDerivedRestriction
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.RingedSectionLocalization
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.AlgebraicGeometry.TorsionCompletionDefinitions

/-! # Constant coefficients and local power-torsion towers

Source: Stacks Project, Tags 099P and 099Q (1), (4), (5)
(blueprint: def-weil-pbc-torsion-completion-sheaf-model).

We use the existing coefficient-sized small model of the unchanged small pro-etale site.
It is equivalent via AsSmall.down to X.ProEt; its topology is the induced topology.
Thus this changes sizes only, not objects, covers, slices, or coefficient sheaves up to
canonical equivalence. Local completeness is the existing slice internal-Hom definition.
The extended ideal is constructed as the kernel of the constant quotient map.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe t u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Use the standard localization at quasi-isomorphisms for the module-sheaf category.
Source: Stacks Tags 05RU, 099Q
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
abbrev TorsionCompletionDerived (X : Scheme.{t}) (A : Type u) [CommRing A] :=
  @DerivedCategory (TorsionCompletionModules X A) _ _ (HasDerivedCategory.standard _)

/-- The localization functor for this choice of derived-category universe.
Source: Stacks Tags 05RU, 099Q
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
def torsionCompletionLocalization (X : Scheme.{t}) (A : Type u) [CommRing A] :
    CochainComplex (TorsionCompletionModules X A) ℤ ⥤ TorsionCompletionDerived X A :=
  @DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)

/-- Derived completeness is the recorded vanishing condition on every slice and for
 every section of the extended ideal. The standard derived categories are chosen on
 all slices as well; no additional existence hypothesis is imposed.
Source: Stacks Tags 0999, 099F, 099Q
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
def IsTorsionCompletionComplete (X : Scheme.{t}) {A : Type u} [CommRing A] (I : Ideal A)
    (K : TorsionCompletionDerived X A) : Prop :=
  letI := HasDerivedCategory.standard (TorsionCompletionModules X A)
  letI : ∀ U : coefficientProEtaleSiteModel.{t, u} X,
      HasDerivedCategory.{max u (t + 1) + 1} (ringedSiteModules.{max u (t + 1)}
        ((sheafCompose _
          (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj
            ((torsionCompletionRing X A).over U))) :=
    fun _ ↦ HasDerivedCategory.standard _
  IsLocallyDerivedRingedIdealComplete (torsionCompletionRing X A)
    (torsionCompletionIdeal X I) (torsionCompletionIdealInclusion X I) K

/-- Degree-zero derived completeness of a sheaf.
Source: Stacks Tag 099Q (1)
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
def IsTorsionCompletionCompleteSheaf (X : Scheme.{t}) {A : Type u} [CommRing A]
    (I : Ideal A) (F : TorsionCompletionModules X A) : Prop :=
  IsTorsionCompletionComplete X I ((torsionCompletionLocalization X A).obj
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F))

/-- An ideal subsheaf annihilates a module if every one of its local sections acts by zero.
This expresses sheaf annihilation, with no section-finiteness hypothesis.
Source: Stacks Tag 099P
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
def IsAnnihilatedByModuleIdeal {C : Type v} [SmallCategory C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{v})
    (M : SheafOfModules.{v} R)
    (ι : M ⟶ SheafOfModules.unit R) (F : SheafOfModules.{v} R) : Prop :=
  ∀ (U : C) (y : M.val.obj (op U)) (x : F.val.obj (op U)),
    ι.val.app (op U) y • x = 0

/-- Locally F is an ordinary countable inverse limit, with level n indexed by the
positive exponent n+1. The covering sieve condition includes every object and arbitrary
further slices. Transition maps have no epimorphism condition.
Source: Stacks Tags 099P, 099Q (4)
(blueprint: def-weil-pbc-torsion-completion-sheaf-model). -/
def IsLocallyPowerTorsionLimit (X : Scheme.{t}) {A : Type u} [CommRing A] (I : Ideal A)
    (F : TorsionCompletionModules X A) : Prop :=
  ∀ U : coefficientProEtaleSiteModel.{t, u} X,
    ∃ S : Sieve U, S ∈ coefficientProEtaleModelTopology.{t, u} X U ∧
      ∀ (V : coefficientProEtaleSiteModel.{t, u} X) (f : V ⟶ U), S f →
        ∃ (G : ℕ → SheafOfModules.{max u (t + 1)}
            ((torsionCompletionModuleRing X A).over V))
          (g : ∀ n : ℕ, G (n + 1) ⟶ G n),
          (∀ n : ℕ, IsAnnihilatedByModuleIdeal
            ((torsionCompletionModuleRing X A).over V)
            ((torsionCompletionIdeal X (I ^ (n + 1))).over V)
            ((torsionCompletionIdealInclusion X (I ^ (n + 1))).over V) (G n)) ∧
          Nonempty (F.over V ≅ limit (Functor.ofOpSequence g))

end AlgebraicGeometry.Scheme
