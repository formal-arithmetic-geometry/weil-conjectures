/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Vector.VectorPurityScalarSingle
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
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
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.SheafRingDerivedHomComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
public import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantInd
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import WeilConjectures.CategoryTheory.DerivedCategory.EssentiallyConstantPro
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedPointwiseKanBridge
public import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
public import WeilConjectures.AlgebraicGeometry.Finite.Tate.FiniteTateSiteDescent

/-! # Data for normalized finite Tate scalar comparisons

Source: main-20261015, sec-smooth-purity/sk-prop-an,
cor-pur-vector-bundle-purity.proof.md, paragraph 2; Stacks 06YN, 06YY, 07A6 and 07A4
(blueprint: lem-pur-finite-tate-scalar-source-normalization).

The balancing isomorphisms are uniquely specified on the existing local Tate generators.
The line and source arrows below use the actual scalar/single, shift, tensor and pullback
comparisons. The theorem asserts invertibility and both boundary normalization equations.

## Main declarations

* `finiteTateScalarLineMap`, `finiteTateScalarSourceMap`: the specified derived arrows.
* The normalization predicates display their ordinary balancing and unit equations.
* `finite_tate_scalar_source_normalization`: flat-single computation and all comparisons.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v₁ v₂ v₃ v₄ w₁ w₂ w₃ w₄
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension Etale.derivedTensor Etale.upperStar Etale.lowerStar
  WeilConjectures.PurityFiniteSetting.purityScalarSingleMap
  WeilConjectures.PurityFiniteSetting.purityScalarUnitMap
namespace WeilConjectures.PurityFiniteSetting

variable {A B : Type (u + 1)} [CommRing A] [CommRing B]

/-- Place the existing ordinary Tate sheaf in degree zero and shift by its even degree.
Source: sk-prop-an, paragraph 2
(blueprint: lem-pur-finite-tate-scalar-source-normalization). -/
abbrev finiteTateScalarObject (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (T : Scheme.{u}) (r : ℕ) : Etale.DerivedCategoryModule A T :=
  ((DerivedCategory.singleFunctor _ 0).obj
    (Scheme.finiteEtaleTateTwist T N A hA r))⟦2 * (r : ℤ)⟧

/-- The zero twist's specified single/unit and zero-shift identifications.
Source: sk-prop-an, paragraph 2 and Stacks 07A4
(blueprint: lem-pur-finite-tate-scalar-source-normalization). -/
def finiteTateScalarZeroIso (A : Type (u + 1)) [CommRing A] (N : ℕ)
    (hA : (N : A) = 0) (T : Scheme.{u}) :
    finiteTateScalarObject A N hA T 0 ≅ 𝟙_ (Etale.DerivedCategoryModule A T) :=
  (shiftFunctorZero _ ℤ).app _ ≪≫
    Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) T

/-- Shift the actual scalar/single adjunct and then apply the given ordinary balancing.
Source: Stacks 06YY, 07A6; sk-prop-an, paragraph 2
(blueprint: lem-pur-finite-tate-scalar-source-normalization). -/
def finiteTateScalarLineMap (φ : A →+* B) (N : ℕ)
    (hA : (N : A) = 0) (hB : (N : B) = 0) (T : Scheme.{u}) (r : ℕ)
    (β : (Etale.purityScalarSheaf φ T).obj (Scheme.finiteEtaleTateTwist T N A hA r) ≅
      Scheme.finiteEtaleTateTwist T N B hB r) :
    (Etale.purityScalarExtension φ T).obj (finiteTateScalarObject A N hA T r) ⟶
      finiteTateScalarObject B N hB T r :=
  (Etale.FiniteSmoothPurity.scalarShiftIso φ T (2 * (r : ℤ))).hom.app _ ≫
    (purityScalarSingleMap φ T (Scheme.finiteEtaleTateTwist T N A hA r) ≫
      (DerivedCategory.singleFunctor _ 0).map β.hom)⟦2 * (r : ℤ)⟧'

/-- The specified source arrow: scalar tensorator, scalar/pullback comparison, then line.
Source: Stacks 07A4; sk-prop-an, paragraph 2
(blueprint: lem-pur-finite-tate-scalar-source-normalization). -/
def finiteTateScalarSourceMap (φ : A →+* B) (N : ℕ)
    (hA : (N : A) = 0) (hB : (N : B) = 0) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (r : ℕ)
    (β : (Etale.purityScalarSheaf φ X).obj (Scheme.finiteEtaleTateTwist X N A hA r) ≅
      Scheme.finiteEtaleTateTwist X N B hB r) (K : Etale.DerivedCategoryModule A Y) :
    (Etale.purityScalarExtension φ X).obj
        (L(Etale.upperStar (ModuleCat.{u + 1} A) f).obj K ⊗
          finiteTateScalarObject A N hA X r) ⟶
      L(Etale.upperStar (ModuleCat.{u + 1} B) f).obj
          ((Etale.purityScalarExtension φ Y).obj K) ⊗ finiteTateScalarObject B N hB X r :=
  (Etale.purityScalarTensor φ X _ _).hom ≫
    ((Etale.purityScalarPullback φ f).hom.app K ⊗ₘ
      finiteTateScalarLineMap φ N hA hB X r β)

attribute [local irreducible] finiteTateScalarZeroIso finiteTateScalarLineMap
  finiteTateScalarSourceMap

/-- Generator, zero-power and ordinary tensor-power normalization.
Source: sk-prop-an, paragraph 2; Stacks 07A4
(blueprint: lem-pur-finite-tate-scalar-source-normalization). -/
def IsFiniteTateScalarBalancing
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (X : Scheme.{u})
    (β : ∀ r : ℕ,
      (Etale.purityScalarSheaf φ X).obj (Scheme.finiteEtaleTateTwist X N A hA r) ≅
        Scheme.finiteEtaleTateTwist X N B hB r) : Prop :=
      (∀ (r : ℕ) (U : X.Etaleᵒᵖ) (a : A) (b : B)
          (z : Fin r → (X.rootsOfUnitySheaf N).obj.obj U),
        ((β r).hom.hom.app U)
            (b • @id (((Etale.purityScalarSheaf φ X).obj
              (Scheme.finiteEtaleTateTwist X N A hA r)).obj.obj U)
              (((Etale.purityScalarSheafAdjunction φ X).unit.app
                (Scheme.finiteEtaleTateTwist X N A hA r)).hom.app U
                  (Scheme.finiteTateEtalePowerGenerator X A N hA U a r z))) =
          Scheme.finiteTateEtalePowerGenerator X B N hB U (φ a * b) r z) ∧
      ((β 0).hom = Functor.OplaxMonoidal.η (Etale.purityScalarSheaf φ X)) ∧
      (∀ r : ℕ, (β (r + 2)).hom =
        Functor.OplaxMonoidal.δ (Etale.purityScalarSheaf φ X)
          (Scheme.finiteEtaleTateTwist X N A hA (r + 1))
          (Scheme.finiteEtaleTateTwist X N A hA 1) ≫
            ((β (r + 1)).hom ⊗ₘ (β 1).hom))

/-- Single/unit and shifted-line invertibility and zero-power normalization.
Source: sk-prop-an, paragraph 2; Stacks 07A4
(blueprint: lem-pur-finite-tate-scalar-source-normalization). -/
def IsFiniteTateScalarLineNormalized
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (X : Scheme.{u})
    (β : ∀ r : ℕ,
      (Etale.purityScalarSheaf φ X).obj (Scheme.finiteEtaleTateTwist X N A hA r) ≅
        Scheme.finiteEtaleTateTwist X N B hB r) : Prop :=
      (purityScalarSingleMap φ X (𝟙_ _) ≫
        (DerivedCategory.singleFunctor _ 0).map (β 0).hom = purityScalarUnitMap φ X) ∧
      (∀ r : ℕ, IsIso (finiteTateScalarLineMap φ N hA hB X r (β r))) ∧
      (finiteTateScalarLineMap φ N hA hB X 0 (β 0) ≫
          (finiteTateScalarZeroIso B N hB X).hom =
        (Etale.purityScalarExtension φ X).map (finiteTateScalarZeroIso A N hA X).hom ≫
          (Etale.ExceptionalCoefficients.unitIso φ X).hom)

/-- Invertibility of the specified source comparison on every unbounded input.
Source: sk-prop-an, paragraph 2; Stacks 07A4
(blueprint: lem-pur-finite-tate-scalar-source-normalization). -/
def IsFiniteTateScalarSourceInvertible
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (X : Scheme.{u})
    (β : ∀ r : ℕ,
      (Etale.purityScalarSheaf φ X).obj (Scheme.finiteEtaleTateTwist X N A hA r) ≅
        Scheme.finiteEtaleTateTwist X N B hB r) : Prop :=
      (∀ (Y : Scheme.{u}) (_hY : ∀ y : Y, IsUnit (N : Y.presheaf.stalk y))
          (f : X ⟶ Y) (K : Etale.DerivedCategoryModule A Y) (r : ℕ),
        IsIso (finiteTateScalarSourceMap φ N hA hB f r (β r) K))

/-- The left-unit diagram, with functor endpoints shared before site specialization.
Source: sk-prop-an, paragraph 2; Stacks 07A4
(blueprint: lem-pur-finite-tate-scalar-source-normalization). -/
def IsFiniteTateScalarLeftUnitEquation
    {C : Type v₁} {D : Type v₂} {E : Type v₃} {F : Type v₄}
    [Category.{w₁} C] [Category.{w₂} D] [Category.{w₃} E] [Category.{w₄} F]
    [MonoidalCategory C] [MonoidalCategory D]
    (Q : C ⥤ D) (R : E ⥤ F) (P : E ⥤ C) (P' : F ⥤ D)
    (U : E) (U' : F) (L : C) (L' : D)
    (s : Q.obj (P.obj U ⊗ L) ⟶ P'.obj (R.obj U) ⊗ L')
    (q : R.obj U ⟶ U') (p : P.obj U ⟶ 𝟙_ C) (p' : P'.obj U' ⟶ 𝟙_ D)
    (l : Q.obj L ⟶ L') : Prop :=
  s ≫ ((P'.map q ≫ p') ▷ L') ≫ (λ_ L').hom =
    Q.map ((p ▷ L) ≫ (λ_ L).hom) ≫ l

/-- The right-unit diagram, with functor endpoints shared before site specialization.
Source: sk-prop-an, paragraph 2; Stacks 07A4
(blueprint: lem-pur-finite-tate-scalar-source-normalization). -/
def IsFiniteTateScalarRightUnitEquation
    {C : Type v₁} {D : Type v₂} {E : Type v₃} {F : Type v₄}
    [Category.{w₁} C] [Category.{w₂} D] [Category.{w₃} E] [Category.{w₄} F]
    [MonoidalCategory C] [MonoidalCategory D]
    (Q : C ⥤ D) (R : E ⥤ F) (P : E ⥤ C) (P' : F ⥤ D)
    (K : E) (L : C) (L' : D)
    (s : Q.obj (P.obj K ⊗ L) ⟶ P'.obj (R.obj K) ⊗ L')
    (e : L ≅ 𝟙_ C) (e' : L' ≅ 𝟙_ D)
    (c : Q.obj (P.obj K) ⟶ P'.obj (R.obj K)) : Prop :=
  s ≫ (P'.obj (R.obj K) ◁ e'.hom) ≫ (ρ_ _).hom =
    Q.map ((P.obj K ◁ e.hom) ≫ (ρ_ _).hom) ≫ c

/-- The coefficient-unit source equation with its specified single/unit maps.
Source: sk-prop-an, paragraph 2; Stacks 07A4
(blueprint: lem-pur-finite-tate-scalar-source-normalization). -/
def IsFiniteTateScalarSourceUnitNormalized
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (X : Scheme.{u})
    (β : ∀ r : ℕ,
      (Etale.purityScalarSheaf φ X).obj (Scheme.finiteEtaleTateTwist X N A hA r) ≅
        Scheme.finiteEtaleTateTwist X N B hB r) : Prop :=
  ∀ (Y : Scheme.{u}) (_hY : ∀ y : Y, IsUnit (N : Y.presheaf.stalk y))
      (f : X ⟶ Y) (r : ℕ),
    IsFiniteTateScalarLeftUnitEquation
      (Etale.purityScalarExtension φ X) (Etale.purityScalarExtension φ Y)
      L(Etale.upperStar (ModuleCat.{u + 1} A) f)
      L(Etale.upperStar (ModuleCat.{u + 1} B) f)
      ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _))
      ((DerivedCategory.singleFunctor _ 0).obj (𝟙_ _))
      (finiteTateScalarObject A N hA X r) (finiteTateScalarObject B N hB X r)
      (finiteTateScalarSourceMap φ N hA hB f r (β r) _)
      (purityScalarUnitMap φ Y)
      (L(Etale.upperStar (ModuleCat.{u + 1} A) f).map
          (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} A) Y).hom ≫
        (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) f).hom)
      (L(Etale.upperStar (ModuleCat.{u + 1} B) f).map
          (Etale.singleFunctorObjUnitIso (ModuleCat.{u + 1} B) Y).hom ≫
        (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} B) f).hom)
      (finiteTateScalarLineMap φ N hA hB X r (β r))

/-- The zero-power source equation with its specified right unitors.
Source: sk-prop-an, paragraph 2; Stacks 07A4
(blueprint: lem-pur-finite-tate-scalar-source-normalization). -/
def IsFiniteTateScalarSourceZeroNormalized
    (φ : A →+* B) (N : ℕ) (hA : (N : A) = 0) (hB : (N : B) = 0)
    (X : Scheme.{u})
    (β : ∀ r : ℕ,
      (Etale.purityScalarSheaf φ X).obj (Scheme.finiteEtaleTateTwist X N A hA r) ≅
        Scheme.finiteEtaleTateTwist X N B hB r) : Prop :=
  ∀ (Y : Scheme.{u}) (_hY : ∀ y : Y, IsUnit (N : Y.presheaf.stalk y))
      (f : X ⟶ Y) (K : Etale.DerivedCategoryModule A Y),
    IsFiniteTateScalarRightUnitEquation
      (Etale.purityScalarExtension φ X) (Etale.purityScalarExtension φ Y)
      L(Etale.upperStar (ModuleCat.{u + 1} A) f)
      L(Etale.upperStar (ModuleCat.{u + 1} B) f) K
      (finiteTateScalarObject A N hA X 0) (finiteTateScalarObject B N hB X 0)
      (finiteTateScalarSourceMap φ N hA hB f 0 (β 0) K)
      (finiteTateScalarZeroIso A N hA X) (finiteTateScalarZeroIso B N hB X)
      ((Etale.purityScalarPullback φ f).hom.app K)

end WeilConjectures.PurityFiniteSetting
