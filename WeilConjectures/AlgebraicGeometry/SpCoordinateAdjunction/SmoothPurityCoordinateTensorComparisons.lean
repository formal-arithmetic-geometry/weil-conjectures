/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateCategories
public import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartAdmissibility
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.SmoothPurityTowerP1Adjunction
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekCalculus
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Kummer.PurityFiniteKummerLevel
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.SmoothPurity.AmbTateRootProjectionReduction
import WeilConjectures.AlgebraicGeometry.Finite.FiniteRootSiteComparison
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTwistLine
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.SmoothPurity.RootTowerFiniteTensor

/-! # Ordered coordinate adjunctions on ordinary derived towers

Source: blueprint latest, sec-smooth-purity/sk-prop-sp-tower-geometric,
`sk-prop-sp-tower-geometric-gluing.proof.md`, Local pairs and Levels
(blueprint: def-sp-coordinate-tate-tensor-comparisons).

All levels n denote exponent n+1. The full subcategories below have uniform bounds,
without normalization. Every arrow belongs to an ordinary derived tower category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u v v' w w' z z'
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpCoordinateAdjunction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The degree-zero Tate line in the actual tower derived category.
Source: Tate factors in Local pairs (blueprint: def-sp-coordinate-tate-tensor-comparisons). -/
abbrev line {T : Scheme.{u}} (w : SpChartAdmissibility.Twists l E T) (r : ℕ) :=
  (DerivedCategory.singleFunctor (SpTowerShriek.S l E T) 0).obj (w.tower r)

/-- The single complex representing that same strict line.
Source: termwise Tate construction (blueprint: def-sp-coordinate-tate-tensor-comparisons). -/
abbrev lineComplex {T : Scheme.{u}} (w : SpChartAdmissibility.Twists l E T) (r : ℕ) :=
  (CochainComplex.singleFunctor (SpTowerShriek.S l E T) 0).obj (w.tower r)

/-- Pure-tensor normalized multiplication on the strict Tate towers, with the
actual K-flat representative equation for the derived map. The ordinary transition
condition is already part of each tower morphism.
Source: Local pairs, tensor reassociation
(blueprint: def-sp-coordinate-tate-tensor-comparisons). -/
structure Products (b : SpTowerShriek.Base l E) {T : Scheme.{u}}
    (w : SpChartAdmissibility.Twists l E T) where
  finite : ∀ n : ℕ, SpEllTwistProducts l E T n
  finite_normalized : ∀ n : ℕ,
    SheafOfModules.SignedLineProductNormalized.{u + 1, u, u + 1}
      (spEllTwistOne l E T n) (finite n)
  ordinary : ∀ a c : ℕ,
    SemilinearSections.ordinaryTensor.{u + 1, u, u + 1}
      (coefficientSequenceTopology (ProEt.topology T))
      (SemilinearSections.systemRing.{u + 1, u, u + 1}
        (ProEt.topology T) (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))
      (w.tower a) (w.tower c) ≅ w.tower (a + c)
  ordinary_normalized : ∀ (a c n : ℕ) (U : T.ProEtᵒᵖ)
    (x : ((SpTowerShriek.ev l E T n).obj (w.tower a)).val.obj U)
    (y : ((SpTowerShriek.ev l E T n).obj (w.tower c)).val.obj U),
    ((SpTowerShriek.ev l E T n).map (ordinary a c).hom ≫
        (w.level n (a + c)).hom).val.app U
      ((SemilinearSections.ordinaryEvaluationTensor.{u + 1, u, u + 1}
        (ProEt.topology T) (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T)
          n (w.tower a) (w.tower c)).inv.val.app U
        (SemilinearSections.tensorSection.{u + 1, u, u + 1}
          (ProEt.topology T) (SpTowerShriek.B l E T n)
          ((SpTowerShriek.ev l E T n).obj (w.tower a))
          ((SpTowerShriek.ev l E T n).obj (w.tower c)) U x y)) =
      (finite n (a : ℤ) (c : ℤ)).hom.val.app U
        (SheafOfModules.siteSheafTensorTmul
          (spEllTwistLine l E T n (a : ℤ)) (spEllTwistLine l E T n (c : ℤ)) U
          ((w.level n a).hom.val.app U x) ((w.level n c).hom.val.app U y))
  kflat : ∀ r : ℕ, CochainComplex.IsKFlatIndependentCoefficients
    (J := coefficientSequenceTopology (ProEt.topology T))
    (R := SpTowerClasses.systemRing l E T) (lineComplex l E w r)
  chain : ∀ a c : ℕ,
    ((SemilinearSections.totalTensor.{u + 1, u, u + 1}
      (coefficientSequenceTopology (ProEt.topology T))
      (SemilinearSections.systemRing.{u + 1, u, u + 1}
        (ProEt.topology T) (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))).obj
      (lineComplex l E w a, lineComplex l E w c)) ⟶ lineComplex l E w (a + c)
  chain_normalized : ∀ a c : ℕ,
    SemilinearSections.tensorSummand.{u + 1, u, u + 1}
      (coefficientSequenceTopology (ProEt.topology T))
      (SemilinearSections.systemRing.{u + 1, u, u + 1}
        (ProEt.topology T) (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))
      (lineComplex l E w a) (lineComplex l E w c) 0 0 0 (by decide) ≫
        (chain a c).f 0 =
      SemilinearSections.ordinaryTensorHom.{u + 1, u, u + 1}
        (coefficientSequenceTopology (ProEt.topology T))
      (SemilinearSections.systemRing.{u + 1, u, u + 1}
        (ProEt.topology T) (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (w.tower a)).hom
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (w.tower c)).hom ≫
        (ordinary a c).hom ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (w.tower (a + c))).inv
  derived : ∀ a c : ℕ,
    (SpTowerShriek.tensor l E b T).obj (line l E w a, line l E w c) ≅ line l E w (a + c)
  derived_normalized : ∀ a c : ℕ,
    (SpTowerShriek.tensor l E b T).map
      (Prod.mkHom
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app (w.tower a))
        ((DerivedCategory.singleFunctorIsoCompQ _ 0).hom.app (w.tower c))) ≫
      (SemilinearSections.tensorModelIso.{u + 1, u, u + 1}
        (coefficientSequenceTopology (ProEt.topology T))
      (SemilinearSections.systemRing.{u + 1, u, u + 1}
        (ProEt.topology T) (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T))
        (b.calculus T).closed (b.calculus T).tensorModels
        (lineComplex l E w a) (lineComplex l E w c) (kflat a) (kflat c)).inv ≫
      DerivedCategory.Q.map (chain a c) ≫
      (DerivedCategory.singleFunctorIsoCompQ _ 0).inv.app (w.tower (a + c)) =
        (derived a c).hom

/-- The canonical total-complex shift in the first tensor variable, with the same
coefficient-size instances as the recorded tensor model. Source: Local pairs,
addition of shifts (blueprint: def-sp-coordinate-tate-tensor-comparisons). -/
def totalShiftFirst (T : Scheme.{u})
    (P Q : CochainComplex (SpTowerShriek.S l E T) ℤ) (n : ℤ) :
    (SemilinearSections.totalTensor.{u + 1, u, u + 1}
      (coefficientSequenceTopology (ProEt.topology T)) (SpTowerClasses.systemRing l E T)).obj
        (P⟦n⟧, Q) ≅
      ((SemilinearSections.totalTensor.{u + 1, u, u + 1}
        (coefficientSequenceTopology (ProEt.topology T)) (SpTowerClasses.systemRing l E T)).obj
          (P, Q))⟦n⟧ := by
  letI := SemilinearSections.abelianSheafify.{u + 1, u, u + 1}
    (coefficientSequenceTopology (ProEt.topology T))
  letI := SemilinearSections.locallyBijective.{u + 1, u, u + 1}
    (coefficientSequenceTopology (ProEt.topology T))
  letI := SheafOfModules.isMonoidal_W_independentCoefficients (SpTowerClasses.systemRing l E T)
  letI := SheafOfModules.monoidalCategory (SpTowerClasses.systemRing l E T)
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
    (SpTowerClasses.systemRing l E T)
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
    (SpTowerClasses.systemRing l E T)
  exact CochainComplex.mapBifunctorShift₁Iso P Q (MonoidalCategory.curriedTensor _) n

/-- The canonical total-complex shift in the second tensor variable, retaining the
Koszul sign. Source: Local pairs (blueprint: def-sp-coordinate-tate-tensor-comparisons). -/
def totalShiftSecond (T : Scheme.{u})
    (P Q : CochainComplex (SpTowerShriek.S l E T) ℤ) (n : ℤ) :
    (SemilinearSections.totalTensor.{u + 1, u, u + 1}
      (coefficientSequenceTopology (ProEt.topology T)) (SpTowerClasses.systemRing l E T)).obj
        (P, Q⟦n⟧) ≅
      ((SemilinearSections.totalTensor.{u + 1, u, u + 1}
        (coefficientSequenceTopology (ProEt.topology T)) (SpTowerClasses.systemRing l E T)).obj
          (P, Q))⟦n⟧ := by
  letI := SemilinearSections.abelianSheafify.{u + 1, u, u + 1}
    (coefficientSequenceTopology (ProEt.topology T))
  letI := SemilinearSections.locallyBijective.{u + 1, u, u + 1}
    (coefficientSequenceTopology (ProEt.topology T))
  letI := SheafOfModules.isMonoidal_W_independentCoefficients (SpTowerClasses.systemRing l E T)
  letI := SheafOfModules.monoidalCategory (SpTowerClasses.systemRing l E T)
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
    (SpTowerClasses.systemRing l E T)
  letI := SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
    (SpTowerClasses.systemRing l E T)
  exact CochainComplex.mapBifunctorShift₂Iso P Q (MonoidalCategory.curriedTensor _) n

/-- Shift comparisons fixed on every K-flat representative of the actual system
category. Source: Local pairs (blueprint: def-sp-coordinate-tate-tensor-comparisons). -/
structure TensorShifts (b : SpTowerShriek.Base l E) (T : Scheme.{u}) where
  first : ∀ (M N : SpTowerShriek.D l E T) (n : ℤ),
    (SpTowerShriek.tensor l E b T).obj (M⟦n⟧, N) ≅
      ((SpTowerShriek.tensor l E b T).obj (M, N))⟦n⟧
  second : ∀ (M N : SpTowerShriek.D l E T) (n : ℤ),
    (SpTowerShriek.tensor l E b T).obj (M, N⟦n⟧) ≅
      ((SpTowerShriek.tensor l E b T).obj (M, N))⟦n⟧
  /-- Naturality of the first-variable shift comparison in both derived inputs.
  This transports the comparison across the isomorphisms used by the derived tensor model.
  Source: tensor shift transport (blueprint: def-sp-coordinate-tate-tensor-comparisons). -/
  first_naturality : ∀ {M₁ M₂ N₁ N₂ : SpTowerShriek.D l E T}
    (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) (n : ℤ),
    (SpTowerShriek.tensor l E b T).map
        (Prod.mkHom ((shiftFunctor _ n).map f) g) ≫
      (first M₂ N₂ n).hom =
    (first M₁ N₁ n).hom ≫
      (shiftFunctor _ n).map
        ((SpTowerShriek.tensor l E b T).map (Prod.mkHom f g))
  /-- Naturality of the second-variable shift comparison in both derived inputs.
  This is the analogous transport law for the second tensor slot.
  Source: tensor shift transport (blueprint: def-sp-coordinate-tate-tensor-comparisons). -/
  second_naturality : ∀ {M₁ M₂ N₁ N₂ : SpTowerShriek.D l E T}
    (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) (n : ℤ),
    (SpTowerShriek.tensor l E b T).map
        (Prod.mkHom f ((shiftFunctor _ n).map g)) ≫
      (second M₂ N₂ n).hom =
    (second M₁ N₁ n).hom ≫
      (shiftFunctor _ n).map
        ((SpTowerShriek.tensor l E b T).map (Prod.mkHom f g))
  first_normalized : ∀ (P Q : CochainComplex (SpTowerShriek.S l E T) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (ProEt.topology T))
      (R := SpTowerClasses.systemRing l E T) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (ProEt.topology T))
      (R := SpTowerClasses.systemRing l E T) Q) (n : ℤ),
    ∃ hPn : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (ProEt.topology T))
      (R := SpTowerClasses.systemRing l E T) (P⟦n⟧),
    (SemilinearSections.tensorModelIso.{u + 1, u, u + 1}
      (coefficientSequenceTopology (ProEt.topology T)) (SpTowerClasses.systemRing l E T)
      (b.calculus T).closed (b.calculus T).tensorModels (P⟦n⟧) Q hPn hQ).hom ≫
      (SpTowerShriek.tensor l E b T).map
        (Prod.mkHom ((DerivedCategory.Q.commShiftIso n).hom.app P) (𝟙 _)) ≫
      (first (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) n).hom ≫
      (shiftFunctor _ n).map
        (SemilinearSections.tensorModelIso.{u + 1, u, u + 1}
          (coefficientSequenceTopology (ProEt.topology T)) (SpTowerClasses.systemRing l E T)
          (b.calculus T).closed (b.calculus T).tensorModels P Q hP hQ).inv =
      DerivedCategory.Q.map (totalShiftFirst l E T P Q n).hom ≫
        (DerivedCategory.Q.commShiftIso n).hom.app
          ((SemilinearSections.totalTensor.{u + 1, u, u + 1}
            (coefficientSequenceTopology (ProEt.topology T))
            (SpTowerClasses.systemRing l E T)).obj (P, Q))
  second_normalized : ∀ (P Q : CochainComplex (SpTowerShriek.S l E T) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (ProEt.topology T))
      (R := SpTowerClasses.systemRing l E T) P)
    (hQ : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (ProEt.topology T))
      (R := SpTowerClasses.systemRing l E T) Q) (n : ℤ),
    ∃ hQn : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (ProEt.topology T))
      (R := SpTowerClasses.systemRing l E T) (Q⟦n⟧),
    (SemilinearSections.tensorModelIso.{u + 1, u, u + 1}
      (coefficientSequenceTopology (ProEt.topology T)) (SpTowerClasses.systemRing l E T)
      (b.calculus T).closed (b.calculus T).tensorModels P (Q⟦n⟧) hP hQn).hom ≫
      (SpTowerShriek.tensor l E b T).map
        (Prod.mkHom (𝟙 _) ((DerivedCategory.Q.commShiftIso n).hom.app Q)) ≫
      (second (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) n).hom ≫
      (shiftFunctor _ n).map
        (SemilinearSections.tensorModelIso.{u + 1, u, u + 1}
          (coefficientSequenceTopology (ProEt.topology T)) (SpTowerClasses.systemRing l E T)
          (b.calculus T).closed (b.calculus T).tensorModels P Q hP hQ).inv =
      DerivedCategory.Q.map (totalShiftSecond l E T P Q n).hom ≫
        (DerivedCategory.Q.commShiftIso n).hom.app
          ((SemilinearSections.totalTensor.{u + 1, u, u + 1}
            (coefficientSequenceTopology (ProEt.topology T))
            (SpTowerClasses.systemRing l E T)).obj (P, Q))

end AlgebraicGeometry.ProEtale.SpCoordinateAdjunction
