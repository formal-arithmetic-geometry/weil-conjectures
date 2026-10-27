# CategoryTheory.NormalizedLimitSquare.Coherence

## Reason

The existing dependent structure expands four normalized corner records, four dependent
comparison records and nine large equation fields in its generated inductive type. The
server profiler measured about eight seconds in its kernel check alone. Repeated
expansion made the fully proved module exceed the 60-second limit. The same data are now
an iterated dependent pair and the same equations a conjunction; `Coherence` is their
existential package. The nine equations are stated directly in `SquareLaws` in this same module.
`augmentation` is exactly `Q.map (limit.lift cone) ≫ unit`; `towerMap` is the existing
termwise natural transformation with its source and target explicitly typed. There are
no new assumptions, no omitted equations, and no arbitrary witness or postponed data.

The dependent-pair fields are ordered corner0, corner1, corner2, corner3, comparisonF,
comparisonG, comparisonH, comparisonK. `SquareData` supplies the same component names.
The old `Coherence` structure constructor/recursor is replaced by existential construction;
there are no current Lean consumers. An existential witness `d` provides components as `d.corner0`, etc.; its accompanying
proof provides all nine conjuncts of `SquareLaws`. No existing Lean consumer needs adaptation.
The target statements are untouched. Any target using this definition transitively should
receive the normal renewed meaning review; all original mathematical clauses remain.

## Old

```lean
structure Coherence (e : F ⋙ G ≅ H ⋙ K) where
  corner0 : Corner L0 eta0
  corner1 : Corner L1 eta1
  corner2 : Corner L2 eta2
  corner3 : Corner L3 eta3
  comparisonF : Comparison corner0 corner1 F
  comparisonG : Comparison corner1 corner3 G
  comparisonH : Comparison corner0 corner2 H
  comparisonK : Comparison corner2 corner3 K
  product_square : ∀ N : ℕ → A0,
    G.map (piComparison F N) ≫ piComparison G (fun n ↦ F.obj (N n)) ≫
        Limits.Pi.map (fun n ↦ e.hom.app (N n)) =
      e.hom.app (∏ᶜ N) ≫ K.map (piComparison H N) ≫
        piComparison K (fun n ↦ H.obj (N n))
  product_projection : ∀ (N : ℕ → A0) (n : ℕ),
    (G.map (piComparison F N) ≫ piComparison G (fun k ↦ F.obj (N k)) ≫
      Limits.Pi.map (fun k ↦ e.hom.app (N k))) ≫
        Pi.π (fun k ↦ K.obj (H.obj (N k))) n =
      G.map (F.map (Pi.π N n)) ≫ e.hom.app (N n)
  projection_naturality : ∀ (N : ℕ → A0) (n : ℕ),
    G.map (F.map (Pi.π N n)) ≫ e.hom.app (N n) =
      e.hom.app (∏ᶜ N) ≫ K.map (H.map (Pi.π N n))
  chain_square : ∀ X : CochainComplex (ℕᵒᵖ ⥤ A0) ℤ,
    (G.mapHomologicalComplex (.up ℤ)).map (comparisonF.kappa.hom.app X) ≫
        comparisonG.kappa.hom.app ((towerComplex F).obj X) ≫
        roosF.map ((NatTrans.mapHomologicalComplex
          ((Functor.whiskeringRight ℕᵒᵖ A0 A3).map e.hom) (.up ℤ)).app X) =
      (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app (roosF.obj X) ≫
        (K.mapHomologicalComplex (.up ℤ)).map (comparisonH.kappa.hom.app X) ≫
        comparisonK.kappa.hom.app ((towerComplex H).obj X)
  roos_square : ∀ M : DerivedCategory.{w0} (ℕᵒᵖ ⥤ A0),
    G.mapDerivedCategory.map (comparisonF.derivedKappa.hom.app M) ≫
        comparisonG.derivedKappa.hom.app ((towerDerived F).obj M) ≫
        corner3.roos.map ((towerSquare F G H K e).hom.app M) =
      (Functor.mapDerivedCategorySquareIso e).hom.app (corner0.roos.obj M) ≫
        K.mapDerivedCategory.map (comparisonH.derivedKappa.hom.app M) ≫
        comparisonK.derivedKappa.hom.app ((towerDerived H).obj M)
  normalized_square : ∀ M : DerivedCategory.{w0} (ℕᵒᵖ ⥤ A0),
    G.mapDerivedCategory.map (comparisonF.lambda.hom.app M) ≫
        comparisonG.lambda.hom.app ((towerDerived F).obj M) ≫
        L3.map ((towerSquare F G H K e).hom.app M) =
      (Functor.mapDerivedCategorySquareIso e).hom.app (L0.obj M) ≫
        K.mapDerivedCategory.map (comparisonH.lambda.hom.app M) ≫
        comparisonK.lambda.hom.app ((towerDerived H).obj M)
  augmentationFG : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A0) ℤ)
    (P : CochainComplex A0 ℤ) (gamma : (Functor.const ℕᵒᵖ).obj P ⟶ X.asFunctor),
    G.mapDerivedCategory.map (F.mapDerivedCategory.map
        (DerivedCategory.Q.map (limit.lift X.asFunctor ⟨P, gamma⟩) ≫ eta0.app X)) ≫
      G.mapDerivedCategory.map
        (comparisonF.lambda.hom.app (DerivedCategory.Q.obj X)) ≫
      comparisonG.lambda.hom.app ((towerDerived F).obj (DerivedCategory.Q.obj X)) ≫
      L3.map ((towerDerived G).map ((towerFactors F).hom.app X)) ≫
      L3.map ((towerFactors G).hom.app ((towerComplex F).obj X)) =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map (limit.lift _
        ((G.mapHomologicalComplex (.up ℤ)).mapCone
          ((F.mapHomologicalComplex (.up ℤ)).mapCone ⟨P, gamma⟩))) ≫
      eta3.app ((towerComplex G).obj ((towerComplex F).obj X))
  augmentationHK : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A0) ℤ)
    (P : CochainComplex A0 ℤ) (gamma : (Functor.const ℕᵒᵖ).obj P ⟶ X.asFunctor),
    K.mapDerivedCategory.map (H.mapDerivedCategory.map
        (DerivedCategory.Q.map (limit.lift X.asFunctor ⟨P, gamma⟩) ≫ eta0.app X)) ≫
      K.mapDerivedCategory.map
        (comparisonH.lambda.hom.app (DerivedCategory.Q.obj X)) ≫
      comparisonK.lambda.hom.app ((towerDerived H).obj (DerivedCategory.Q.obj X)) ≫
      L3.map ((towerDerived K).map ((towerFactors H).hom.app X)) ≫
      L3.map ((towerFactors K).hom.app ((towerComplex H).obj X)) =
    K.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app P) ≫
      K.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map (limit.lift _
        ((K.mapHomologicalComplex (.up ℤ)).mapCone
          ((H.mapHomologicalComplex (.up ℤ)).mapCone ⟨P, gamma⟩))) ≫
      eta3.app ((towerComplex K).obj ((towerComplex H).obj X))
  augmentation_square : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ A0) ℤ)
    (P : CochainComplex A0 ℤ) (gamma : (Functor.const ℕᵒᵖ).obj P ⟶ X.asFunctor),
    DerivedCategory.Q.map (limit.lift _
        ((G.mapHomologicalComplex (.up ℤ)).mapCone
          ((F.mapHomologicalComplex (.up ℤ)).mapCone ⟨P, gamma⟩))) ≫
      eta3.app ((towerComplex G).obj ((towerComplex F).obj X)) ≫
      L3.map (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        ((Functor.whiskeringRight ℕᵒᵖ A0 A3).map e.hom) (.up ℤ)).app X)) =
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) ≫
      DerivedCategory.Q.map (limit.lift _
        ((K.mapHomologicalComplex (.up ℤ)).mapCone
          ((H.mapHomologicalComplex (.up ℤ)).mapCone ⟨P, gamma⟩))) ≫
      eta3.app ((towerComplex K).obj ((towerComplex H).obj X))
```

## New

```lean
def SquareData :=
  Σ a0 : Corner L0 eta0, Σ a1 : Corner L1 eta1,
    Σ a2 : Corner L2 eta2, Σ a3 : Corner L3 eta3,
      Comparison a0 a1 F × Comparison a1 a3 G ×
        Comparison a0 a2 H × Comparison a2 a3 K

/-- The `corner0` component of the fixed comparison data.
Source: the normalized square construction
(blueprint: lem-cbc-normalized-limit-square-coherence). -/
abbrev SquareData.corner0 (d : SquareData F G H K L0 eta0 L1 eta1 L2 eta2 L3 eta3) :=
  d.1

/-- The `corner1` component of the fixed comparison data.
Source: the normalized square construction
(blueprint: lem-cbc-normalized-limit-square-coherence). -/
abbrev SquareData.corner1 (d : SquareData F G H K L0 eta0 L1 eta1 L2 eta2 L3 eta3) :=
  d.2.1

/-- The `corner2` component of the fixed comparison data.
Source: the normalized square construction
(blueprint: lem-cbc-normalized-limit-square-coherence). -/
abbrev SquareData.corner2 (d : SquareData F G H K L0 eta0 L1 eta1 L2 eta2 L3 eta3) :=
  d.2.2.1

/-- The `corner3` component of the fixed comparison data.
Source: the normalized square construction
(blueprint: lem-cbc-normalized-limit-square-coherence). -/
abbrev SquareData.corner3 (d : SquareData F G H K L0 eta0 L1 eta1 L2 eta2 L3 eta3) :=
  d.the project server

/-- The `comparisonF` component of the fixed comparison data.
Source: the normalized square construction
(blueprint: lem-cbc-normalized-limit-square-coherence). -/
abbrev SquareData.comparisonF (d : SquareData F G H K L0 eta0 L1 eta1 L2 eta2 L3 eta3) :=
  d.the project server.1

/-- The `comparisonG` component of the fixed comparison data.
Source: the normalized square construction
(blueprint: lem-cbc-normalized-limit-square-coherence). -/
abbrev SquareData.comparisonG (d : SquareData F G H K L0 eta0 L1 eta1 L2 eta2 L3 eta3) :=
  d.the project server.2.1

/-- The `comparisonH` component of the fixed comparison data.
Source: the normalized square construction
(blueprint: lem-cbc-normalized-limit-square-coherence). -/
abbrev SquareData.comparisonH (d : SquareData F G H K L0 eta0 L1 eta1 L2 eta2 L3 eta3) :=
  d.the project server.2.2.1

/-- The `comparisonK` component of the fixed comparison data.
Source: the normalized square construction
(blueprint: lem-cbc-normalized-limit-square-coherence). -/
abbrev SquareData.comparisonK (d : SquareData F G H K L0 eta0 L1 eta1 L2 eta2 L3 eta3) :=
  d.the project server.2.2.2

/-- All equations attached to one fixed square of comparisons.
Source: the square and augmentation calculation
(blueprint: lem-cbc-normalized-limit-square-coherence). -/
def SquareLaws (d : SquareData F G H K L0 eta0 L1 eta1 L2 eta2 L3 eta3)
    (e : F ⋙ G ≅ H ⋙ K) : Prop :=
  (∀ N : ℕ → A0,
  G.map (piComparison F N) ≫ piComparison G (fun n ↦ F.obj (N n)) ≫
      Limits.Pi.map (fun n ↦ e.hom.app (N n)) =
    e.hom.app (∏ᶜ N) ≫ K.map (piComparison H N) ≫
      piComparison K (fun n ↦ H.obj (N n))) ∧
  (∀ (N : ℕ → A0) (n : ℕ),
  (G.map (piComparison F N) ≫ piComparison G (fun k ↦ F.obj (N k)) ≫
    Limits.Pi.map (fun k ↦ e.hom.app (N k))) ≫
      Pi.π (fun k ↦ K.obj (H.obj (N k))) n =
    G.map (F.map (Pi.π N n)) ≫ e.hom.app (N n)) ∧
  (∀ (N : ℕ → A0) (n : ℕ),
  G.map (F.map (Pi.π N n)) ≫ e.hom.app (N n) =
    e.hom.app (∏ᶜ N) ≫ K.map (H.map (Pi.π N n))) ∧
  (∀ X : CochainComplex (ℕᵒᵖ ⥤ A0) ℤ,
  (G.mapHomologicalComplex (.up ℤ)).map (d.comparisonF.kappa.hom.app X) ≫
      d.comparisonG.kappa.hom.app ((towerComplex F).obj X) ≫
      roosF.map ((towerMap F G H K e.hom).app X) =
    (NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app (roosF.obj X) ≫
      (K.mapHomologicalComplex (.up ℤ)).map (d.comparisonH.kappa.hom.app X) ≫
      d.comparisonK.kappa.hom.app ((towerComplex H).obj X)) ∧
  (∀ M : DerivedCategory.{w0} (ℕᵒᵖ ⥤ A0),
  G.mapDerivedCategory.map (d.comparisonF.derivedKappa.hom.app M) ≫
      d.comparisonG.derivedKappa.hom.app ((towerDerived F).obj M) ≫
      d.corner3.roos.map ((towerSquare F G H K e).hom.app M) =
    (Functor.mapDerivedCategorySquareIso e).hom.app (d.corner0.roos.obj M) ≫
      K.mapDerivedCategory.map (d.comparisonH.derivedKappa.hom.app M) ≫
      d.comparisonK.derivedKappa.hom.app ((towerDerived H).obj M)) ∧
  (∀ M : DerivedCategory.{w0} (ℕᵒᵖ ⥤ A0),
  G.mapDerivedCategory.map (d.comparisonF.lambda.hom.app M) ≫
      d.comparisonG.lambda.hom.app ((towerDerived F).obj M) ≫
      L3.map ((towerSquare F G H K e).hom.app M) =
    (Functor.mapDerivedCategorySquareIso e).hom.app (L0.obj M) ≫
      K.mapDerivedCategory.map (d.comparisonH.lambda.hom.app M) ≫
      d.comparisonK.lambda.hom.app ((towerDerived H).obj M)) ∧
  (∀ (X : CochainComplex (ℕᵒᵖ ⥤ A0) ℤ)
  (P : CochainComplex A0 ℤ) (gamma : (Functor.const ℕᵒᵖ).obj P ⟶ X.asFunctor),
  G.mapDerivedCategory.map (F.mapDerivedCategory.map (augmentation ⟨P, gamma⟩ (eta0.app X))) ≫
    G.mapDerivedCategory.map (d.comparisonF.lambda.hom.app (DerivedCategory.Q.obj X)) ≫
    d.comparisonG.lambda.hom.app ((towerDerived F).obj (DerivedCategory.Q.obj X)) ≫
    L3.map ((towerDerived G).map ((towerFactors F).hom.app X)) ≫
    L3.map ((towerFactors G).hom.app ((towerComplex F).obj X)) =
  G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
    G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
    augmentation ((G.mapHomologicalComplex (.up ℤ)).mapCone
        ((F.mapHomologicalComplex (.up ℤ)).mapCone ⟨P, gamma⟩)) (eta3.app ((towerComplex G).obj
          ((towerComplex F).obj X)))) ∧
  (∀ (X : CochainComplex (ℕᵒᵖ ⥤ A0) ℤ)
  (P : CochainComplex A0 ℤ) (gamma : (Functor.const ℕᵒᵖ).obj P ⟶ X.asFunctor),
  K.mapDerivedCategory.map (H.mapDerivedCategory.map (augmentation ⟨P, gamma⟩ (eta0.app X))) ≫
    K.mapDerivedCategory.map (d.comparisonH.lambda.hom.app (DerivedCategory.Q.obj X)) ≫
    d.comparisonK.lambda.hom.app ((towerDerived H).obj (DerivedCategory.Q.obj X)) ≫
    L3.map ((towerDerived K).map ((towerFactors H).hom.app X)) ≫
    L3.map ((towerFactors K).hom.app ((towerComplex H).obj X)) =
  K.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app P) ≫
    K.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj P) ≫
    augmentation ((K.mapHomologicalComplex (.up ℤ)).mapCone
        ((H.mapHomologicalComplex (.up ℤ)).mapCone ⟨P, gamma⟩)) (eta3.app ((towerComplex K).obj
          ((towerComplex H).obj X)))) ∧
  (∀ (X : CochainComplex (ℕᵒᵖ ⥤ A0) ℤ)
  (P : CochainComplex A0 ℤ) (gamma : (Functor.const ℕᵒᵖ).obj P ⟶ X.asFunctor),
  augmentation ((G.mapHomologicalComplex (.up ℤ)).mapCone
        ((F.mapHomologicalComplex (.up ℤ)).mapCone ⟨P, gamma⟩)) (eta3.app ((towerComplex G).obj
          ((towerComplex F).obj X))) ≫
    L3.map (DerivedCategory.Q.map ((towerMap F G H K e.hom).app X)) =
  DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) ≫
    augmentation ((K.mapHomologicalComplex (.up ℤ)).mapCone
        ((H.mapHomologicalComplex (.up ℤ)).mapCone ⟨P, gamma⟩)) (eta3.app ((towerComplex K).obj
          ((towerComplex H).obj X))))

/-- All clauses of square coherence, with the very same corners and comparisons.
Fields are conclusions, and specify actual chain maps and natural isomorphisms.
Source: the final blueprint comparison paragraph and the DAG's projection calculation
(blueprint: lem-cbc-normalized-limit-square-coherence). -/
def Coherence (e : F ⋙ G ≅ H ⋙ K) :=
  ∃ d : SquareData F G H K L0 eta0 L1 eta1 L2 eta2 L3 eta3,
    SquareLaws F G H K L0 eta0 L1 eta1 L2 eta2 L3 eta3 d e
```

Unfolding `SquareLaws`, `augmentation` and `towerMap` recovers the original nine
equations up to definitional equality and associativity of composition.
The old `Nonempty` of a record and the new `Nonempty` of an existence proposition
assert exactly the same existence, with all eight data components and all nine laws.

The `towerSquare` construction is unchanged; it now omits section instances for
countable products, tower limits and base derived categories, which its body does not
use. This reduces repeated elaboration while retaining every actual dependency.

## Users

`python3 tools/downstream.py Sheaf.Paper.NormalizedLimitSquareCoherence --uses Coherence
Comparison towerSquare Corner` reports zero downstream Lean modules. The textual uses
are confined to the item. DAG parents retain the same node and mathematical statement;
no node or module is withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.NormalizedLimitSquareCoherence | B9 | Equivalent concrete representation; complete proof |

## Status

landed 20261024T184637-L-3086306 2026-10-24 (merge of deliver/B9/Sheaf.Paper.NormalizedLimitSquareCoherence)
