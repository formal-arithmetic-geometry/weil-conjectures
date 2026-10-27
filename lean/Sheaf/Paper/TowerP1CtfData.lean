/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A5
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Sheaf.Paper.SmoothPurityCoefficientTowers
public import Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import Sheaf.Paper.SmoothPurityTowerClasses
public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import Sheaf.Paper.SmoothPurityTowerBound
public import Sheaf.AlgebraicGeometry.EtalePullbackLineFlatModel
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import Sheaf.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine

/-! # Data for uniform projective-line coefficient-tower domains

Source: the definitions of lem-sp-tower-p1-uniform-ctf-domains, factored out
without changing their bodies so that its proof steps can import them.
(blueprint: def-sp-tower-p1-ctf-data) -/

@[expose] public noncomputable section

set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerP1Uniform

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The proper tower image, in the original coefficient-tower coordinates.
Source: standing-setting restriction, proper q
(blueprint: lem-sp-tower-p1-uniform-ctf-domains). -/
def push {S : Scheme.{u}} {hS : IsUnit (l : Γ(S, ⊤))}
    (c : TowerClasses l E S hS)
    (DS : SpCoefficientTowersAbelian l E S)
    (DP : SpCoefficientTowersAbelian l E (ProjectiveLine S)) :=
  (spTowerShriekRealization l E c.base (ProjectiveLine S) DP).functor ⋙
    SpTowerShriek.push l E c.base c.projective.geometry ⋙
      (spTowerShriekRealization l E c.base S DS).inverse

/-- Exact tower inverse image, derived tensor with the recorded Tate line, and shift two.
Source: standing-setting restriction, q^*(-)(1)[2]
(blueprint: lem-sp-tower-p1-uniform-ctf-domains). -/
def pullTwist {S : Scheme.{u}} {hS : IsUnit (l : Γ(S, ⊤))}
    (c : TowerClasses l E S hS)
    (DS : SpCoefficientTowersAbelian l E S)
    (DP : SpCoefficientTowersAbelian l E (ProjectiveLine S)) :=
  (spTowerShriekRealization l E c.base S DS).functor ⋙
    SpTowerShriek.pull l E c.base c.projective.geometry ⋙
      Prod.sectL (SpTowerShriek.D l E (ProjectiveLine S))
        ((SpTowerClasses.line l E c.chernP)⟦(2 : ℤ)⟧) ⋙
      SpTowerShriek.tensor l E c.base (ProjectiveLine S) ⋙
        (spTowerShriekRealization l E c.base (ProjectiveLine S) DP).inverse

/-- The prescribed cohomological and Tor intervals, using intrinsic constructibility
with finite locally closed constructible stratifications, at every positive level.
Source: the more precise bounds (blueprint: lem-sp-tower-p1-uniform-ctf-domains). -/
def bounds (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (K : spDerivedCoefficientTowers l E T D) (r s a b : ℤ) : Prop :=
  ∀ n : ℕ,
    DerivedCategory.IsGE ((spDerivedCoefficientEvaluation l E T D n).obj K) r ∧
    DerivedCategory.IsLE ((spDerivedCoefficientEvaluation l E T D n).obj K) s ∧
    (∀ i : ℤ, Scheme.IsConstructibleProEtaleModuleSheaf T (SpTowerShriek.R l E n)
      ((DerivedCategory.homologyFunctor _ i).obj
        ((spDerivedCoefficientEvaluation l E T D n).obj K))) ∧
    Scheme.HasProEtaleTorAmplitude T (SpTowerShriek.R l E n)
      ((spDerivedCoefficientEvaluation l E T D n).obj K) a b

/-- The literal termwise comparison pullback of the specified etale complex,
followed by the canonical associated-module-sheaf realization.
Source: the local pro-etale K-flat model
(blueprint: lem-sp-tower-p1-uniform-ctf-domains). -/
def comparisonModel (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (C : CochainComplex
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A))) ℤ) :=
  ((finiteCoefficientIntrinsicRealization T A).mapHomologicalComplex (.up ℤ)).obj
    (((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T)
      |>.mapHomologicalComplex (.up ℤ)).obj C)

/-- The actual etale inverse-image, root-line tensor and shift-two complex.
Source: the prescribed local model (blueprint: lem-sp-tower-p1-uniform-ctf-domains). -/
def lineModel (A : Type u) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (T : Scheme.{u})
    (C : CochainComplex
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A))) ℤ) :=
  Etale.etalePullbackLineModel (ULift.{u + 1} A) (ProjectiveLine T ↘ T) C
    (Scheme.finiteEtaleTateLine (ProjectiveLine T) N (ULift.{u + 1} A)
      (ULift.ext _ _ hA)) 2

/-- Retained etale and flat representatives, their specified pullback-line model, and
its actual pro-etale realization. The stratum clause is the existing pulled-back
stratification assertion, including finite local module values and common covers.
Source: the affine-local and global representative clauses; Stacks 03TT, 0963, 06YQ
(blueprint: lem-sp-tower-p1-uniform-ctf-domains). -/
structure LocalModel (A : Type u) [CommRing A] [Finite A] (N : ℕ) (hA : (N : A) = 0)
    (T : Scheme.{u}) (K : Scheme.proEtaleDerivedCategory T A)
    (G : Scheme.proEtaleDerivedCategory (ProjectiveLine T) A) (r s a b : ℤ) where
  etale : DerivedCategory.Plus
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A)))
  etale_constructible : Etale.DerivedCategory.boundedConstructible
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) T etale.obj
  etale_lower : DerivedCategory.IsGE etale.obj r
  etale_upper : DerivedCategory.IsLE etale.obj s
  etale_tor : Etale.DerivedCategory.hasTorAmplitudeIn (ULift.{u + 1} A) T a b etale.obj
  origin : (finiteCoefficientIntrinsicRealization T A).mapDerivedCategory.obj
    ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) T)
      |>.mapDerivedCategory.obj etale.obj) ≅ K
  complex : CochainComplex
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} A))) ℤ
  represents : DerivedCategory.Q.obj complex ≅ etale.obj
  flat : Etale.IsBoundedFlatComplex (ULift.{u + 1} A) a b complex
  terms_constructible : ∀ i : ℤ, Scheme.IsConstructibleEtaleModuleSheaf (complex.X i)
  cover : Scheme.Cover.{u} Scheme.etalePrecoverage (ProjectiveLine T)
  line_trivial : ∀ i : cover.I₀, Nonempty
    ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) (cover.f i)).obj
      (Scheme.finiteEtaleTateLine (ProjectiveLine T) N (ULift.{u + 1} A)
        (ULift.ext _ _ hA)) ≅
      (constantSheaf (cover.X i).smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} A))).obj
          (ModuleCat.of (ULift.{u + 1} A) (ULift.{u + 1} A)))
  strata : Etale.etalePullbackLineAssertions (ULift.{u + 1} A)
    (ProjectiveLine T ↘ T) complex etale.obj represents
    (Scheme.finiteEtaleTateLine (ProjectiveLine T) N (ULift.{u + 1} A)
      (ULift.ext _ _ hA)) 2 a b cover
  pro_flat : ∀ i : ℤ, SheafOfModules.IsFlatOnSite
    (J := Scheme.ProEt.topology (ProjectiveLine T))
    (R := Scheme.proEtaleConstantRing (ProjectiveLine T) A)
    ((comparisonModel (ProjectiveLine T) A (lineModel A N hA T complex)).X i)
  pro_support : ∀ i : ℤ, (i < a - 2 ∨ b - 2 < i) → IsZero
    ((comparisonModel (ProjectiveLine T) A (lineModel A N hA T complex)).X i)
  pro_kflat : CochainComplex.IsKFlatIndependentCoefficients
    (R := Scheme.proEtaleConstantRing (ProjectiveLine T) A)
    (comparisonModel (ProjectiveLine T) A (lineModel A N hA T complex))
  pro_represents : DerivedCategory.Q.obj
    (comparisonModel (ProjectiveLine T) A (lineModel A N hA T complex)) ≅ G


end AlgebraicGeometry.ProEtale.SpTowerP1Uniform
