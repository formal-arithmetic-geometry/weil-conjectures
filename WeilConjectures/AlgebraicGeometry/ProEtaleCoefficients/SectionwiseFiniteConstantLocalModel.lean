/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantRingedLocalModel
public import WeilConjectures.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor
public import WeilConjectures.CategoryTheory.Site.SiteDerivedConstantModuleFunctor
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
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
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
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
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! # Sectionwise finite constant local models

Source: blueprint, sk-def-sfb-constructible, clause 1; Stacks 03CY and 03EK
(blueprint: sk-def-sfb-constructible).

The existing ringed-site and internal condensed-module definitions remain available
through the public import. This companion interface expresses the scalar local-model
clause on the chosen small site in sectionwise module sheaves.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe r
open CategoryTheory
namespace AlgebraicGeometry.ProEtale

variable {C : Type r} [SmallCategory C] (J : GrothendieckTopology C)
  (A : Type r) [CommRing A] (B : Sheaf J CommRingCat.{r})
  (σ : realizationRing J A ⟶ B)

/-- A specified scalar model on a covering object: finite presentation is over the scalar
ring before sheafification, and extension uses the actual coefficient morphism.
Source: blueprint sk-def-sfb-constructible, clause 1; Stacks 03CY, 03EK
(blueprint: sk-def-sfb-constructible). -/
def HasFiniteScalarConstantModelOn
    (L : SheafOfModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J B))
    (U : C) (N : ModuleCat.{r} A) : Prop :=
  Module.FinitePresentation A N ∧ Nonempty (L.over U ≅
    (SheafOfModules.changeOfRings σ ((commutativeSiteConstantModuleFunctor J A).obj N)).over U)

/-- The scalar local-model condition, imposed on a covering sieve of every site object.
It allows empty covering sieves and zero scalar modules. Source: blueprint
sk-def-sfb-constructible, clause 1; Stacks 03CY, 03EK
(blueprint: sk-def-sfb-constructible). -/
def HasFiniteScalarConstantLocalModel
    (L : SheafOfModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J B)) :
    Prop :=
  ∀ V : C, ∃ W : Sieve V, W ∈ J V ∧ ∀ (U : C) (f : U ⟶ V), W f →
    ∃ N : ModuleCat.{r} A, HasFiniteScalarConstantModelOn J A B σ L U N

end AlgebraicGeometry.ProEtale
