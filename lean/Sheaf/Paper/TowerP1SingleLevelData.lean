/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.Paper.TowerP1EtaleOriginComparisons
public import Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison
public import Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.AlgebraicGeometry.FixedEtaleOriginWitness
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace

/-! # Single-level realization and conditional finite projective-line triangles

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-tower-geometric/sk-prop-sp-tower-geometric-p1.proof.md, Levels;
the expanded single-level argument in det-sp-tower-p1-adjunction, steps 10--11
(blueprint: def-sp-tower-p1-single-level-data).

Index n denotes the paper's positive level n+1. We retain the actual varying-ring
system category, fixed-scalar etale antecedents, and the normalized comparison words.
The singleton and its coordinate are existential conclusions, never extra hypotheses.
The finite triangles are conditional on the two specified tower triangles.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
  AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.SpTowerP1

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (n : ℕ) [Finite (SpTowerShriek.R l E n)]

/-- The exact singleton, characterized by its specified coordinate at n, zero objects
elsewhere, and zero adjacent transitions. Its localization is required to lie in C+.
This is data in the conclusion, not an assumption of singleton existence. All sections,
scalars and arrows are those of the already recorded system category.
Source: Levels, single-level construction
(blueprint: def-sp-tower-p1-single-level-data). -/
structure SingleLevelRealization (b : SpTowerShriek.Base l E) (T : Scheme.{u}) where
  singleton : FixedSheaves l E n T ⥤ SpTowerShriek.S l E T
  [additive : singleton.Additive]
  [limits : PreservesFiniteLimits singleton]
  [colimits : PreservesFiniteColimits singleton]
  coordinate : singleton ⋙ SpTowerShriek.ev l E T n ≅ realization l E n T
  zero_levels : ∀ (m : ℕ), m ≠ n → ∀ N : FixedSheaves l E n T,
    IsZero ((SpTowerShriek.ev l E T m).obj (singleton.obj N))
  zero_transitions : ∀ (N : FixedSheaves l E n T) (m : ℕ) (U : T.ProEtᵒᵖ),
    (singleton.obj N).val.map (Prod.mkHom (homOfLE (Nat.le_succ m)) (𝟙 U.unop)).op = 0
  range : ∀ L : DerivedCategory.Plus
    (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (levelRing l E n))),
    domain l E b T
      (((comparisonUpperStar (ModuleCat.{u + 1} (levelRing l E n)) T) ⋙
        singleton).mapDerivedCategory.obj L.obj)

attribute [instance] SingleLevelRealization.additive SingleLevelRealization.limits
  SingleLevelRealization.colimits

/-- Localization of the exact termwise comparison/singleton composite, restricted to
bounded-below inputs. Thus it is independent of any representative. Exact localization
provides the shift and triangle structure on its ambient derived functor.
Source: Levels; Stacks 015F
(blueprint: def-sp-tower-p1-single-level-data). -/
def SingleLevelRealization.J {b : SpTowerShriek.Base l E} {T : Scheme.{u}}
    (j : SingleLevelRealization l E n b T) :
    DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (levelRing l E n))) ⥤ C l E b T :=
  ObjectProperty.lift _
    (DerivedCategory.Plus.ι ⋙
      ((comparisonUpperStar (ModuleCat.{u + 1} (levelRing l E n)) T) ⋙
        j.singleton).mapDerivedCategory) j.range

/-- The canonical derived level coordinate is the localization of the ordinary
coordinate, including the exact-functor composition comparisons.
Source: Levels (blueprint: def-sp-tower-p1-single-level-data). -/
def SingleLevelRealization.evaluation {b : SpTowerShriek.Base l E} {T : Scheme.{u}}
    (j : SingleLevelRealization l E n b T) :
    j.J l E n ⋙ (domain l E b T).ι ⋙ SpTowerShriek.Ev l E T n ≅
      DerivedCategory.Plus.ι ⋙ nu l E n T :=
  Functor.isoWhiskerLeft DerivedCategory.Plus.ι
    ((Functor.mapDerivedCategoryCompIso _ (SpTowerShriek.ev l E T n)).symm ≪≫
      Functor.mapDerivedCategoryNatIso
        (Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft
            (comparisonUpperStar (ModuleCat.{u + 1} (levelRing l E n)) T) j.coordinate) ≪≫
      Functor.mapDerivedCategoryCompIso _ (realization l E n T))

/-- The level-n witness retains precisely the caller's etale complex. It does not
choose an antecedent from a mere existence proposition.
Source: Levels (blueprint: def-sp-tower-p1-single-level-data). -/
def SingleLevelRealization.origin {b : SpTowerShriek.Base l E} {T : Scheme.{u}}
    (j : SingleLevelRealization l E n b T)
    (L : DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (levelRing l E n)))) :
    SpTowerShriek.Origin l E b T n ((j.J l E n).obj L).obj where
  level := (comparisonUpperStar
    (ModuleCat.{u + 1} (levelRing l E n)) T).mapDerivedCategoryPlus.obj L
  realization := ((j.evaluation l E n).app L).symm
  witness := ⟨L, Iso.refl _⟩

variable {S : Scheme.{u}} {hS : IsUnit (l : Γ(S, ⊤))}
  {p : Presentation l E S hS}

/-- Ordinary etale F_n is exactly the existing total direct image.
Source: Levels (blueprint: def-sp-tower-p1-single-level-data). -/
abbrev singleLevelF (S : Scheme.{u}) :=
  EtaleWords.push (levelRing l E n) (ProjectiveLine S ↘ S)

/-- Ordinary etale G_n is exact inverse image tensored with the existing shifted line.
Source: Levels (blueprint: def-sp-tower-p1-single-level-data). -/
def singleLevelG (S : Scheme.{u}) :=
  EtaleWords.pull (levelRing l E n) (ProjectiveLine S ↘ S) ⋙
    (EtaleWords.tensor (levelRing l E n) (ProjectiveLine S)).flip.obj
      (EtaleWords.line (levelRing l E n) (l ^ (n + 1)) (levelAnnihilates l E n)
        (ProjectiveLine S))

/-- The existing ordinary diagonal formula, with its specified finite coordinates.
Source: Levels (blueprint: def-sp-tower-p1-single-level-data). -/
abbrev singleLevelEta (c : ProjectiveCoordinates l E n p)
    (hD : (diagonalImmersion S).ker.IsInvertible)
    (L : Etale.DerivedCategoryModule (levelRing l E n) (ProjectiveLine S)) :=
  EtaleWords.eta (levelRing l E n) (l ^ (n + 1))
    (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime l)) _) (levelAnnihilates l E n)
    S hD (surfaceExponentUnit l n hS) c.transport c.invertible L

/-- The existing ordinary inverse-projection/splitting-trace formula.
Source: Levels (blueprint: def-sp-tower-p1-single-level-data). -/
abbrev singleLevelEpsilon (c : ProjectiveCoordinates l E n p)
    (H : Etale.DerivedCategoryModule (levelRing l E n) S) :=
  EtaleWords.epsilon (levelRing l E n) (l ^ (n + 1)) (levelAnnihilates l E n)
    S (baseExponentUnit l n hS) c.transport c.splitting c.invertible H

/-- Canonical natural F and G comparisons on the singleton inputs, normalized by the
actual recursively defined word comparisons. The four compatibility fields retain
projection, exchange/composition, classes, and the complete eta/epsilon words for EVERY
origin witness, hence also for FJ, GJ and their iterates.
Source: Levels (blueprint: def-sp-tower-p1-single-level-data). -/
structure SingleLevelComparisons (d : Maps l E p) (h : EtaleOriginComparisons l E p d) where
  base : SingleLevelRealization l E n p.classes.base S
  projective : SingleLevelRealization l E n p.classes.base (ProjectiveLine S)
  coordinates : ProjectiveCoordinates l E n p
  projection : ProjectionLevelComparisons l E n coordinates
  exchange : ExchangeLevelComparisons l E n coordinates
  classes : ClassLevelComparisons l E n coordinates h.cartier_diagonal
  formulas : FormulaLevelComparisons l E n coordinates d h.cartier_diagonal
  push : DerivedCategory.Plus.ι ⋙ singleLevelF l E n S ⋙ nu l E n S ≅
    projective.J l E n ⋙ (domain l E p.classes.base (ProjectiveLine S)).ι ⋙
      p.F l E ⋙ SpTowerShriek.Ev l E S n
  push_eq : ∀ L : DerivedCategory.Plus
    (Sheaf (ProjectiveLine S).smallEtaleTopology (ModuleCat.{u + 1} (levelRing l E n))),
    push.hom.app L =
      (coordinates.push l E n (ProjectiveLine S ↘ S)
        (originWord l E n p.classes.base (projective.origin l E n L))).comparison
  pull : DerivedCategory.Plus.ι ⋙ singleLevelG l E n S ⋙ nu l E n (ProjectiveLine S) ≅
    base.J l E n ⋙ (domain l E p.classes.base S).ι ⋙
      p.G l E ⋙ SpTowerShriek.Ev l E (ProjectiveLine S) n
  pull_eq : ∀ H : DerivedCategory.Plus
    (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (levelRing l E n))),
    pull.hom.app H =
      (coordinates.tensor l E n
        (coordinates.pull l E n (ProjectiveLine S ↘ S)
          (originWord l E n p.classes.base (base.origin l E n H)))
        (coordinates.lineP l E n)).comparison

/-- The complete single-level assertion at fixed normalized geometric data. This
predicate only packages the conclusions; its Finite parameter is supplied by the
recorded coefficient datum in the public theorem, not by an extra hypothesis.
Source: Levels (blueprint: def-sp-tower-p1-single-level-data). -/
def singleLevelTrianglesStatement (S : Scheme.{u}) (hS : IsUnit (l : Γ(S, ⊤)))
    (p : Presentation l E S hS) (d : Maps l E p) (h : EtaleOriginComparisons l E p d) :
    Prop :=
    ∃ c : SingleLevelComparisons l E n d h,
      ((∀ M : C l E p.classes.base (ProjectiveLine S),
        (p.F l E).map (eta l E d M) ≫ epsilon l E d ((left l E d).obj M) =
          𝟙 ((p.F l E).obj M.obj)) ∧
       (∀ K : C l E p.classes.base S,
        eta l E d ((rightRestricted l E d).obj K) ≫ (p.G l E).map (epsilon l E d K) =
          𝟙 ((p.G l E).obj K.obj))) →
      ((∀ L : DerivedCategory.Plus
          (Sheaf (ProjectiveLine S).smallEtaleTopology
            (ModuleCat.{u + 1} (levelRing l E n))),
        (singleLevelF l E n S).map
            (singleLevelEta l E n c.coordinates h.cartier_diagonal L.obj) ≫
          singleLevelEpsilon l E n c.coordinates ((singleLevelF l E n S).obj L.obj) =
            𝟙 ((singleLevelF l E n S).obj L.obj)) ∧
       (∀ H : DerivedCategory.Plus
          (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} (levelRing l E n))),
        singleLevelEta l E n c.coordinates h.cartier_diagonal
            ((singleLevelG l E n S).obj H.obj) ≫
          (singleLevelG l E n S).map (singleLevelEpsilon l E n c.coordinates H.obj) =
            𝟙 ((singleLevelG l E n S).obj H.obj)))


end AlgebraicGeometry.ProEtale.SpTowerP1

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
