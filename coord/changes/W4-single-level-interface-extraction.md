# AlgebraicGeometry.ProEtale.SpTowerP1.SingleLevelRealization

## Reason

Move the unchanged single-level interfaces into a dependency module so the singleton
construction and the unconditional comparison squares can be separate proof items without
an import cycle. This is a proof decomposition, not a timeout workaround. The original
module publicly imports the extracted module, preserving its public declarations and all
its original public imports transitively. Every moved declaration has the same full name,
universe, visibility, signature and body. Only docstring node tags follow the new attachment.
No definition or target meaning changes. No source-library file is changed.

## Old

In `lean/Sheaf/Paper/TowerP1SingleLevelTriangles.lean`, in namespace
`AlgebraicGeometry.ProEtale.SpTowerP1` and the original variable context:

```lean
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
(blueprint: lem-sp-tower-p1-single-level-triangles). -/
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
Source: Levels (blueprint: lem-sp-tower-p1-single-level-triangles). -/
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
Source: Levels (blueprint: lem-sp-tower-p1-single-level-triangles). -/
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
Source: Levels (blueprint: lem-sp-tower-p1-single-level-triangles). -/
abbrev singleLevelF (S : Scheme.{u}) :=
  EtaleWords.push (levelRing l E n) (ProjectiveLine S ↘ S)

/-- Ordinary etale G_n is exact inverse image tensored with the existing shifted line.
Source: Levels (blueprint: lem-sp-tower-p1-single-level-triangles). -/
def singleLevelG (S : Scheme.{u}) :=
  EtaleWords.pull (levelRing l E n) (ProjectiveLine S ↘ S) ⋙
    (EtaleWords.tensor (levelRing l E n) (ProjectiveLine S)).flip.obj
      (EtaleWords.line (levelRing l E n) (l ^ (n + 1)) (levelAnnihilates l E n)
        (ProjectiveLine S))

/-- The existing ordinary diagonal formula, with its specified finite coordinates.
Source: Levels (blueprint: lem-sp-tower-p1-single-level-triangles). -/
abbrev singleLevelEta (c : ProjectiveCoordinates l E n p)
    (hD : (diagonalImmersion S).ker.IsInvertible)
    (L : Etale.DerivedCategoryModule (levelRing l E n) (ProjectiveLine S)) :=
  EtaleWords.eta (levelRing l E n) (l ^ (n + 1))
    (pow_pos (Nat.Prime.pos (Fact.out : Nat.Prime l)) _) (levelAnnihilates l E n)
    S hD (surfaceExponentUnit l n hS) c.transport c.invertible L

/-- The existing ordinary inverse-projection/splitting-trace formula.
Source: Levels (blueprint: lem-sp-tower-p1-single-level-triangles). -/
abbrev singleLevelEpsilon (c : ProjectiveCoordinates l E n p)
    (H : Etale.DerivedCategoryModule (levelRing l E n) S) :=
  EtaleWords.epsilon (levelRing l E n) (l ^ (n + 1)) (levelAnnihilates l E n)
    S (baseExponentUnit l n hS) c.transport c.splitting c.invertible H

/-- Canonical natural F and G comparisons on the singleton inputs, normalized by the
actual recursively defined word comparisons. The four compatibility fields retain
projection, exchange/composition, classes, and the complete eta/epsilon words for EVERY
origin witness, hence also for FJ, GJ and their iterates.
Source: Levels (blueprint: lem-sp-tower-p1-single-level-triangles). -/
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
Source: Levels (blueprint: lem-sp-tower-p1-single-level-triangles). -/
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
```

## New

The same declarations in `lean/Sheaf/Paper/TowerP1SingleLevelData.lean`, with the same
namespace and variable context; docstring node tags identify the extracted interface node:

```lean
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
```

`Sheaf.Paper.TowerP1SingleLevelTriangles` publicly imports
`Sheaf.Paper.TowerP1SingleLevelData`. The item theorem's signature is unchanged.

## Users

`python3 tools/downstream.py Sheaf.Paper.TowerP1SingleLevelTriangles` reports zero
current Lean consumers. This is not a withdrawal: the unfinished DAG parents still need
the original theorem, which stays in its original module with its original statement.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.TowerP1SingleLevelTriangles | W4 | Publicly reexports all moved interfaces. |
| Sheaf.Paper.TowerP1SingleLevelData | new in W4 | Holds the unchanged interfaces. |
| Sheaf.Paper.TowerP1SingleLevelConstruction | new in W4 | States the exact singleton construction. |
| Sheaf.Paper.TowerP1SingleLevelTransport | new in W4 | States unconditional composite-word comparison. |

## Status

landed 20261025T164647-L-1048928 2026-10-25 (merge of deliver/W4/Sheaf.Paper.TowerP1SingleLevelTriangles)
