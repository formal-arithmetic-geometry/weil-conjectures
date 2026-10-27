/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q118
-/
module

public import Sheaf.SixFunctors.SemilinearProperOpenMatePasting
public import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import Sheaf.CategoryTheory.LocalizedModuleExactForSystems
public import WeilConjectures.Compactification.Defs
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Sheaf.Paper.SemilinearCompactifiedGraphData
import Sheaf.AlgebraicGeometry.UnramifiedMorphism
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicOpenUnit
import Sheaf.AlgebraicGeometry.ProEtaleClopenRingedModuleGluing
import Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
import Sheaf.CategoryTheory.ExactSquareDerivedCounit
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-! # Compactified graph maps for semilinear systems

Source: Stacks Project, Tag 0F4L, lemma-shriek-into-star-separated-etale;
blueprint det-sp-tower-gluing, Local pairs and Levels
(blueprint: lem-sp-semilinear-compactified-graph-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Scheme WeilConjectures WeilConjectures.SemilinearSections

namespace CategoryTheory.Functor

variable {A : Type (u + 2)} {B : Type (u + 2)}
  [Category.{u + 1} A] [Category.{u + 1} B] [Abelian A] [Abelian B]
  [HasDerivedCategory.{u + 2} A] [HasDerivedCategory.{u + 2} B]
  [Abelian.HasKInjectiveResolutions A]

/-- The canonical right-derived comparison on a complex, transported from the
homotopy-category right-derived unit. No resolution or comparison is chosen.
Source: Stacks 07A4; blueprint Levels
(blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
def semilinearGraphDerivedComparison (F : A ⥤ B) [F.Additive]
    (K : CochainComplex A ℤ) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso B).inv.app _ ≫
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient A (.up ℤ)).obj K) ≫
      F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso A).hom.app K)

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.SemilinearGraph

variable (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n : ℕ, C (n + 1) ⟶ C n)

/-- Exact localization of the normalized sum comparison.
Source: Zheng 4.10; Stacks 0F4L
(blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
def derivedSumEvaluation {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] (n : ℕ) :=
  letI := levelSumAdditive (C n) e
  letI := levelSumLimits (C n) e
  letI := levelSumColimits (C n) e
  (Functor.mapDerivedCategoryCompIso (sumExtension C τ e) (ev C τ T n)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (sumEvaluation C τ e n) ≪≫
      Functor.mapDerivedCategoryCompIso (ev C τ U n) (levelSum (C n) e)

/-- Exact localization of the normalized open comparison.
Source: Zheng 4.10; Stacks 09AE
(blueprint: lem-sp-semilinear-compactified-graph-evaluation). -/
def derivedOpenEvaluation {U Z : Scheme.{u}} (j : U ⟶ Z) [IsOpenImmersion j] (n : ℕ) :=
  letI := StrictTower.moduleJ_additive (C n) j
  letI := StrictTower.moduleJ_finiteLimits (C n) j
  letI := StrictTower.moduleJ_finiteColimits (C n) j
  (Functor.mapDerivedCategoryCompIso (SemilinearProperOpen.extension C τ j)
    (ev C τ Z n)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (openEvaluation C τ j n) ≪≫
      Functor.mapDerivedCategoryCompIso (ev C τ U n) (StrictTower.moduleJ (C n) j)

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- The graph construction on systems, its localization, and equality of the
specified evaluated natural transformations. Source: Stacks 0F4L,
lemma-shriek-into-star-separated-etale; blueprint det-sp-tower-gluing,
Local pairs and Levels (blueprint: lem-sp-semilinear-compactified-graph-evaluation).

Proof:
1. Etale e is weakly etale. Use weaklyEtale_localization and the constant-ring
identifications to transport extensionByZeroPresheaf and localizedSystemExact.
Componentwise exactness gives exactness on strict semilinear systems.
2. For V -> T with lift t, the graph in the compactification is open, because
its factor through U times_T V is an etale section. It is closed as a section
of the proper, hence separated, projection. This also covers empty V.
3. Use the open-extension unit and clopen_ringed_module_gluing to extend each
m by zero on the complementary clopen. The pair (m,0) proves uniqueness.
4. This pair calculation proves linearity for all local constant-ring sections,
naturality in M and compatibility with pro-etale restrictions.
5. A horizontal transition sends (m,0) to (alpha(m),0); no scalar extension or
flatness is used. Direct-sum elimination and module sheafification give G.
6. Evaluation preserves each summand and the sheafification unit, so G evaluates
to the single-coefficient graph construction, under the specified comparisons.
7. On complexes compose Q(G) with the canonical right-derived comparison gamma.
Naturality and exactness descend this word to the ordinary unbounded derived
category, including inverses of quasi-isomorphisms.
8. Under the canonical derived adjunction, gamma has transpose Q of the ordinary
counit, by exactSquare_derived_counit and K-injective resolutions. Evaluation
preserves that counit and its transpose (semilinearDerivedSections), hence
evaluates gamma to gamma_n. Apply this to j_!K and step 6. This proves equality
of natural transformations; no faithfulness of derived evaluation is asserted.
-/
structure CompactifiedGraphEvaluation
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e] (c : Compactification e) where
  /-- The system map obtained by summing the graph extensions and sheafifying. -/
  graph : sumExtension C τ e ⟶
    SemilinearProperOpen.extension C τ c.i ⋙ SemilinearProperOpen.push C τ c.g
  /-- Unique zero extension on the clopen graph, on every generator. -/
  graph_value : IsGraphMap C τ e c graph
  /-- The induced transformation on the ordinary derived category of systems. -/
  theta : (sumExtension C τ e).mapDerivedCategory ⟶
    SemilinearProperOpen.J C τ c.i ⋙ SemilinearProperOpen.R C τ c.g
  /-- Its value is precisely gamma composed with Q of the graph map. -/
  theta_complex : ∀ K : CochainComplex (SemilinearProperOpen.Modules C τ U) ℤ,
    theta.app (DerivedCategory.Q.obj K) =
      (sumExtension C τ e).mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex graph (.up ℤ)).app K) ≫
      (SemilinearProperOpen.push C τ c.g).semilinearGraphDerivedComparison
        (((SemilinearProperOpen.extension C τ c.i).mapHomologicalComplex (.up ℤ)).obj K) ≫
      (SemilinearProperOpen.R C τ c.g).map
        ((SemilinearProperOpen.extension C τ c.i).mapDerivedCategoryFactors.inv.app K)
  /-- The graph construction with the single ring C_n. -/
  levelGraph : ∀ n : ℕ, levelSum (C n) e ⟶
    StrictTower.moduleJ (C n) c.i ⋙ StrictTower.moduleDirectImage (C n) c.g
  /-- The same clopen graph and unique zero extension at a single level. -/
  level_value : ∀ n : ℕ, IsLevelGraphMap (C n) e c (levelGraph n)
  /-- Equality of ordinary graph maps under section-normalized evaluation. -/
  graph_evaluation : ∀ n : ℕ,
    Functor.whiskerRight graph (ev C τ T n) ≫
      Functor.whiskerLeft (SemilinearProperOpen.extension C τ c.i)
        (pushEvaluation C τ c.g n).hom ≫
      Functor.whiskerRight (openEvaluation C τ c.i n).hom
        (StrictTower.moduleDirectImage (C n) c.g) =
      (sumEvaluation C τ e n).hom ≫ Functor.whiskerLeft (ev C τ U n) (levelGraph n)
  /-- The derived transformation with the single coefficient ring. -/
  levelTheta : ∀ n : ℕ, (levelSum (C n) e).mapDerivedCategory ⟶
    (StrictTower.moduleJ (C n) c.i).mapDerivedCategory ⋙
      (StrictTower.moduleDirectImage (C n) c.g).rightDerivedFunctor
  /-- The single-coefficient transformation is the same gamma-Q(G) word. -/
  level_theta_complex : ∀ (n : ℕ) (K : CochainComplex (StrictTower.Modules (C n) U) ℤ),
    (levelTheta n).app (DerivedCategory.Q.obj K) =
      (levelSum (C n) e).mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex (levelGraph n) (.up ℤ)).app K) ≫
      (StrictTower.moduleDirectImage (C n) c.g).semilinearGraphDerivedComparison
        (((StrictTower.moduleJ (C n) c.i).mapHomologicalComplex (.up ℤ)).obj K) ≫
      (StrictTower.moduleDirectImage (C n) c.g).rightDerivedFunctor.map
        ((StrictTower.moduleJ (C n) c.i).mapDerivedCategoryFactors.inv.app K)
  /-- The simultaneous-operation direct-image evaluation isomorphism. -/
  pushEvaluationDerived : ∀ n : ℕ,
    SemilinearProperOpen.R C τ c.g ⋙ (ev C τ T n).mapDerivedCategory ≅
      (ev C τ c.Z n).mapDerivedCategory ⋙
        (StrictTower.moduleDirectImage (C n) c.g).rightDerivedFunctor
  /-- Its normalization is evaluation of the canonical right-derived unit. -/
  comparison_normalization : ∀ (n : ℕ)
      (K : CochainComplex (SemilinearProperOpen.Modules C τ c.Z) ℤ),
    (ev C τ T n).mapDerivedCategory.map
        ((SemilinearProperOpen.push C τ c.g).semilinearGraphDerivedComparison K) ≫
      (pushEvaluationDerived n).hom.app (DerivedCategory.Q.obj K) ≫
      (StrictTower.moduleDirectImage (C n) c.g).rightDerivedFunctor.map
        ((ev C τ c.Z n).mapDerivedCategoryFactors.hom.app K) =
    (ev C τ T n).mapDerivedCategoryFactors.hom.app
        (((SemilinearProperOpen.push C τ c.g).mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map (pushEvaluationComplex C τ c.g n K) ≫
      (StrictTower.moduleDirectImage (C n) c.g).semilinearGraphDerivedComparison
        (((ev C τ c.Z n).mapHomologicalComplex (.up ℤ)).obj K)
  /-- Equality of natural transformations on the ordinary derived category. -/
  theta_evaluation : ∀ n : ℕ,
    Functor.whiskerRight theta (ev C τ T n).mapDerivedCategory ≫
      Functor.whiskerLeft (SemilinearProperOpen.J C τ c.i) (pushEvaluationDerived n).hom ≫
      Functor.whiskerRight (derivedOpenEvaluation C τ c.i n).hom
        (StrictTower.moduleDirectImage (C n) c.g).rightDerivedFunctor =
      (derivedSumEvaluation C τ e n).hom ≫
        Functor.whiskerLeft (ev C τ U n).mapDerivedCategory (levelTheta n)

/-- Compactified semilinear graph construction, with its full section and
ordinary-derived evaluation normalizations.
Source: Stacks 0F4L; blueprint det-sp-tower-gluing, Local pairs and Levels
(blueprint: lem-sp-semilinear-compactified-graph-evaluation).
Proof: perform steps 1--8 in the docstring of CompactifiedGraphEvaluation:
localize the sheafified sum, extend by zero on clopen graphs, check scalars,
restrictions, naturality and horizontal transitions by uniqueness of (m,0),
sheafify, descend gamma composed with Q(G), and evaluate its counit transpose.
The last equality is of natural transformations on the actual derived systems. -/
theorem semilinear_compactified_graph_evaluation
    {U T : Scheme.{u}} (e : U ⟶ T) [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e] (c : Compactification e) :
    Nonempty (CompactifiedGraphEvaluation C τ e c) := by
  sorry

end AlgebraicGeometry.ProEtale.SemilinearGraph
