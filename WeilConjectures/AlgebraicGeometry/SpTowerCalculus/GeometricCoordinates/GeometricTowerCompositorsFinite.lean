/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.GeometricCoordinates.CoefficientTowerGeometricAssembly
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDirectImageComposition
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCompositionTowerDefinitions
import all WeilConjectures.AlgebraicGeometry.SpTowerCalculus.GeometricCoordinates.GeometricTowerCompositorParts
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.GeometricCoordinates.GeometricTowerCompositorsOpenSquare
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.GeometricCoordinates.GeometricTowerCompositorsProperSquare

/-! # Evaluation of the two tower compositors
Source: Stacks 0F7J, the separate factors of the compatible-tower composition.
(blueprint: lem-sp-geometric-tower-compositors-finite).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerCalculus.GeometricCoordinates


variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem paste_compositor_squares
    {C D : Type*} [Category C] [Category D] (V : C ⥤ D)
    {A B C₀ : C} {S T U : D}
    (a : A ⟶ B) (b : B ⟶ C₀) (c : A ⟶ C₀)
    (x : V.obj A ⟶ S) (y : V.obj B ⟶ T) (z : V.obj C₀ ⟶ U)
    (i : S ⟶ T) (j : T ⟶ U) (k : S ⟶ U)
    (hc : c = a ≫ b) (ha : V.map a ≫ y = x ≫ i)
    (hb : V.map b ≫ z = y ≫ j) (hk : i ≫ j = k) :
    V.map c ≫ z = x ≫ k := by
  rw [hc, Functor.map_comp, Category.assoc, hb, ← Category.assoc, ha,
    Category.assoc, hk]

attribute [local irreducible] _root_.DerivedCategory _root_.instCategoryDerivedCategory
  HasDerivedCategory.standard HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
  nativeCoordinate nativeSupportCoordinates towerIntermediateCoordinates
  Functor.mapDerivedCategory Functor.rightDerivedFunctor

/-- Finite evaluation of only the open and proper compositors. No middle mate,
finite-origin witness, canonical compactification, or common refinement occurs.
Source: Stacks 0F7J (blueprint: lem-sp-geometric-tower-compositors-finite).

Proof: use the preimage identity for nativeTowerCompositors. Its image is the
four-factor graph coordinate, the exact open compositor and total proper
compositor, and the inverse compact-support graph coordinate. At the ordinary
level GraphCoordinates.sections, morphisms, unit_sections, counit_sections and
push_evaluation identify the direct-image comparison with the specified push
section comparison. Taking the unique left adjoint comparisons identifies the
open extension compositor; its composite adjunct is the composite restriction
comparison. Right derivation transports the ordinary proper composition square,
using K-injective representatives and the canonical composition comparison.
Exact localization transports the open square. Evaluate the four original
factors using their given normalized evaluations. Naturality moves each
comparison through its adjacent factor and the unit/counit pairs cancel.
The resulting intrinsic word is finiteTowerIntermediateCoordinates followed by
the canonical fixed open and proper compositors with T.i_q and T.p_g, namely
finiteTowerContraction. The source word is towerIntermediateEvaluation.
ve.normalization identifies the remaining target word with fixedEvaluation.
The same adjunction identities cover identity maps, empty opens and zero inputs. -/
theorem tower_compositors_finite
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)
    (q : Coordinates l E b) (z : FiniteCoordinates l E)
    (g : GraphCoordinates l E b o)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {h : Y ⟶ Z}
    (T : Compactification.Triangle f h) (n : ℕ)
    (ve : Evaluation l E b o q T.cfg n)
    (K : spDerivedCoefficientTowers l E X (q.abelian X)) :
    (fixedLevel l E b q Z n).map ((nativeTowerCompositors l E b o q g T).app K) ≫
      (fixedEvaluation l E b o q z T.cfg n ve).hom.app K =
    (towerIntermediateEvaluation l E b o q T n).hom.app K ≫
      (finiteTowerContraction l E z T n).hom.app
        ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj K)  := by
  have hf := native_compositor_parts l E b o q g T K
  have ho := open_collapse_finite l E b o q z g T n K
  have hp := proper_collapse_finite l E b o q z g T n ve K
  have he := finite_compositor_parts l E z T n
    ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj K)
  have result := paste_compositor_squares (fixedLevel l E b q Z n)
    (openCollapse l E b o q g T K) (properCollapse l E b o q g T K)
    ((nativeTowerCompositors l E b o q g T).app K)
    ((towerIntermediateEvaluation l E b o q T n).hom.app K)
    ((afterOpenEvaluation l E b o q z T n).hom.app K)
    ((fixedEvaluation l E b o q z T.cfg n ve).hom.app K)
    ((finiteOpenCollapse l E z T n).hom.app
      ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj K))
    ((finiteProperCollapse l E T n).hom.app
      ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj K))
    ((finiteTowerContraction l E z T n).hom.app
      ((spDerivedCoefficientEvaluation l E X (q.abelian X) n).obj K)) hf ho hp he
  tower_transport result



end AlgebraicGeometry.ProEtale.SpTowerCalculus.GeometricCoordinates
