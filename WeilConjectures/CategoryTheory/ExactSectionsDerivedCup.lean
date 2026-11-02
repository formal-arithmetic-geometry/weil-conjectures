/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import Mathlib.CategoryTheory.Monoidal.Functor
import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.Algebra.Homology.ProperBaseChange.AlgebraicInverseImageOfTransport
import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonConstruction

/-! # Derived cup for exact sections

Source: Stacks Project, Tags 0FPJ (section-cup-product), 0B6C (remark-cup-product),
and 0FPK (lemma-cup-compatible-with-naive).
(blueprint: lem-sf-exact-sections-derived-cup-map).

The normalization includes every total-tensor summand and the native localization
square. Thus the cup is specified on K-flat representatives, rather than being an
unconstrained morphism between the indicated objects.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe a b r w z c v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped TensorProduct

namespace CategoryTheory

section CupData
variable {B : Type a} [Category.{b} B] [Abelian B]
  [MonoidalCategory B] [MonoidalPreadditive B]
  [∀ (X Y : GradedObject ℤ B), X.HasTensor Y]
  [∀ X, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).obj X)]
  [∀ X, PreservesColimit (Functor.empty.{0} B) ((curriedTensor B).flip.obj X)]
  [∀ (W X Y Z : GradedObject ℤ B), GradedObject.HasTensor₄ObjExt W X Y Z]
  [∀ (X Y Z : GradedObject ℤ B), GradedObject.HasGoodTensor₁₂Tensor X Y Z]
  [∀ (X Y Z : GradedObject ℤ B), GradedObject.HasGoodTensorTensor₂₃ X Y Z]
  {S : Type r} [CommRing S]
  [HasDerivedCategory.{w} B] [HasDerivedCategory.{z} (ModuleCat.{r} S)]
  [MonoidalCategory (DerivedCategory B)]
  [(DerivedCategory.Q : CochainComplex B ℤ ⥤ DerivedCategory B).LaxMonoidal]
  (G : B ⥤ ModuleCat.{r} S) [G.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The cup, together with its ordinary and total-complex normalizations.
Source: Stacks 0FPJ, 0B6C and 0FPK
(blueprint: lem-sf-exact-sections-derived-cup-map).
The two lax structures record naturality and both unit laws. The localization
square determines the derived tensorator on K-flat representatives. -/
structure ExactSectionsDerivedCup where
  ordinary : G.LaxMonoidal
  derived : G.mapDerivedCategory.LaxMonoidal
  chain : ∀ K L : CochainComplex B ℤ,
    (G.mapHomologicalComplex (.up ℤ)).obj K ⊗
      (G.mapHomologicalComplex (.up ℤ)).obj L ⟶
        (G.mapHomologicalComplex (.up ℤ)).obj (K ⊗ L)
  chain_summand : ∀ (K L : CochainComplex B ℤ) (p q n : ℤ) (h : p + q = n),
    HomologicalComplex.ιTensorObj ((G.mapHomologicalComplex (.up ℤ)).obj K)
        ((G.mapHomologicalComplex (.up ℤ)).obj L) p q n h ≫ (chain K L).f n =
      ordinary.μ (K.X p) (L.X q) ≫ G.map (HomologicalComplex.ιTensorObj K L p q n h)
  chainUnit : 𝟙_ (CochainComplex (ModuleCat.{r} S) ℤ) ⟶
    (G.mapHomologicalComplex (.up ℤ)).obj (𝟙_ (CochainComplex B ℤ))
  chainUnit_zero : chainUnit.f 0 =
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{r} S))).hom ≫
      ordinary.ε ≫ G.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ B)).inv
  tensor_normalization : ∀ K L : CochainComplex B ℤ,
    derived.μ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L) ≫
        G.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q K L) ≫
        G.mapDerivedCategoryFactors.hom.app (K ⊗ L) =
      (G.mapDerivedCategoryFactors.hom.app K ⊗ₘ G.mapDerivedCategoryFactors.hom.app L) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((G.mapHomologicalComplex (.up ℤ)).obj K)
          ((G.mapHomologicalComplex (.up ℤ)).obj L) ≫
        DerivedCategory.Q.map (chain K L)
  unit_normalization :
    derived.ε ≫ G.mapDerivedCategory.map (Functor.LaxMonoidal.ε DerivedCategory.Q) ≫
        G.mapDerivedCategoryFactors.hom.app (𝟙_ (CochainComplex B ℤ)) =
      Functor.LaxMonoidal.ε DerivedCategory.Q ≫ DerivedCategory.Q.map chainUnit

end CupData

namespace ExactSectionsDerivedCup

attribute [instance] RingedDerivedNative.monoidal RingedDerivedNative.lax

variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v u}]
  (R : Sheaf J CommRingCat.{max c v u})

section Internal

attribute [instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

variable [(J.W (A := AddCommGrpCat.{max c v u})).IsMonoidal]

open InternalAbelianSheafModule

end Internal
end ExactSectionsDerivedCup
end CategoryTheory
