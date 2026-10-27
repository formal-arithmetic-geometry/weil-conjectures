# Morphism.reductionPullIso_normalized and finite comparison normalizations

## Reason

Profiling the new comparison proofs showed about 50 seconds of kernel checking
for reduction/pullback and 36 seconds for concrete finite-evaluation cancellation.
The concrete tensor and strict-tower equations were repeatedly expanded while
checking specializations. The complete file exceeded the 60-second limit.

## Old

```lean
def Morphism.reductionPullIso_normalized {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A)
    (e : V.reduction A I ⋙ f.towerPull A ≅ f.pull A ⋙ U.reduction A I) : Prop :=
  ∀ P : CochainComplex (V.modules A) ℤ, P.IsAcyclicTensorKFlat →
    (∀ q : ℤ, (P.X q).IsFlat) →
    e.hom.app ((ConstantCompletion.Q (V.ring A)).obj P) ≫
      (U.reduction A I).map ((f.modulePull A).mapDerivedCategoryFactors.hom.app P) ≫
      (ConstantCompletion.quotientPresentation U.topology A I false).comparison.app
        (((f.modulePull A).mapHomologicalComplex (.up ℤ)).obj P) =
    (f.towerPull A).map
        ((ConstantCompletion.quotientPresentation V.topology A I false).comparison.app P) ≫
      (f.towerModulePull A).mapDerivedCategoryFactors.hom.app
        (ConstantCompletion.reductionComplex V.topology A I false P) ≫
      (ConstantCompletion.TQ (U.ring A)).map
        ((f.moduleReductionPullComplexIso A I).hom.app P)
```

```lean
def Site.finiteEvaluationIso_normalized (T : Site.{u}) (A : Type u)
    [CommRing A] (I : Ideal A) (n : ℕ)
    (e : T.reduction A I ⋙ T.evaluate A n ≅
        T.finiteReduction A I n ⋙ T.finiteRestriction A I n) : Prop :=
  ∀ P : CochainComplex (T.modules A) ℤ, P.IsAcyclicTensorKFlat →
    (∀ q : ℤ, (P.X q).IsFlat) →
    e.hom.app ((ConstantCompletion.Q (T.ring A)).obj P) ≫
      (T.finiteRestriction A I n).map
        ((ConstantCompletion.extendComparison
          (ConstantCompletion.quotient T.topology A I n)).app P) =
    (T.evaluate A n).map
        ((ConstantCompletion.quotientPresentation T.topology A I false).comparison.app P) ≫
      ((T.evaluateModule A n).mapDerivedCategoryFactors.hom.app
          (ConstantCompletion.reductionComplex T.topology A I false P) ≫
        (ConstantCompletion.Q (T.ring A)).map
          ((ConstantCompletion.quotientEvaluationComplexIso T.topology A I n).hom.app P)) ≫
      (ConstantCompletion.resFactors (ConstantCompletion.quotient T.topology A I n)).hom.app
        (((ConstantCompletion.change (ConstantCompletion.quotient T.topology A I n)
          ).mapHomologicalComplex (.up ℤ)).obj P)
```

```lean
def Morphism.finitePullIso_normalized {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ)
    (e : f.pull A ⋙ U.finiteReduction A I n ≅
        V.finiteReduction A I n ⋙ f.pull (quotientRing A I n)) : Prop :=
  ∀ P : CochainComplex (V.modules A) ℤ, P.IsAcyclicTensorKFlat →
    (∀ q : ℤ, (P.X q).IsFlat) →
    (U.finiteReduction A I n).map ((f.modulePull A).mapDerivedCategoryFactors.hom.app P) ≫
      (ConstantCompletion.extendComparison (ConstantCompletion.quotient U.topology A I n)).app
        (((f.modulePull A).mapHomologicalComplex (.up ℤ)).obj P) ≫
      (ConstantCompletion.Q (U.ring (quotientRing A I n))).map
        ((ConstantCompletion.mapComplexSquare (f.modulePull A)
          (ConstantCompletion.change (ConstantCompletion.quotient U.topology A I n))
          (ConstantCompletion.change (ConstantCompletion.quotient V.topology A I n))
          (f.modulePull (quotientRing A I n))
          (ConstantCompletion.ordinaryFinitePull f.algebra f.direct f.adjunction A I n)
          ).hom.app P) =
    e.hom.app ((ConstantCompletion.Q (V.ring A)).obj P) ≫
      (f.pull (quotientRing A I n)).map
        ((ConstantCompletion.extendComparison
          (ConstantCompletion.quotient V.topology A I n)).app P) ≫
      (f.modulePull (quotientRing A I n)).mapDerivedCategoryFactors.hom.app
        (((ConstantCompletion.change (ConstantCompletion.quotient V.topology A I n)
          ).mapHomologicalComplex (.up ℤ)).obj P)
```

## New

```lean
def Morphism.reductionPullIso_normalized {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A)
    (e : V.reduction A I ⋙ f.towerPull A ≅ f.pull A ⋙ U.reduction A I) : Prop :=
  ∀ P : CochainComplex (V.modules A) ℤ, P.IsAcyclicTensorKFlat →
    (∀ q : ℤ, (P.X q).IsFlat) →
    comparisonSquareFormula
      (ConstantCompletion.quotientPresentation V.topology A I false).comparison
      (f.towerModulePull A).mapDerivedCategoryFactors.hom
      (f.moduleReductionPullComplexIso A I)
      (f.modulePull A).mapDerivedCategoryFactors.hom
      (ConstantCompletion.quotientPresentation U.topology A I false).comparison e P
```

```lean
def Site.finiteEvaluationIso_normalized (T : Site.{u}) (A : Type u)
    [CommRing A] (I : Ideal A) (n : ℕ)
    (e : T.reduction A I ⋙ T.evaluate A n ≅
        T.finiteReduction A I n ⋙ T.finiteRestriction A I n) : Prop :=
  ∀ P : CochainComplex (T.modules A) ℤ, P.IsAcyclicTensorKFlat →
    (∀ q : ℤ, (P.X q).IsFlat) →
    evaluationSquareFormula
      (ConstantCompletion.quotientPresentation T.topology A I false).comparison
      (T.evaluateModule A n).mapDerivedCategoryFactors.hom
      (ConstantCompletion.quotientEvaluationComplexIso T.topology A I n)
      (ConstantCompletion.extendComparison (ConstantCompletion.quotient T.topology A I n))
      (ConstantCompletion.resFactors (ConstantCompletion.quotient T.topology A I n)) e P
```

```lean
def Morphism.finitePullIso_normalized {V U : Site.{u}} (f : Morphism V U)
    (A : Type u) [CommRing A] (I : Ideal A) (n : ℕ)
    (e : f.pull A ⋙ U.finiteReduction A I n ≅
        V.finiteReduction A I n ⋙ f.pull (quotientRing A I n)) : Prop :=
  ∀ P : CochainComplex (V.modules A) ℤ, P.IsAcyclicTensorKFlat →
    (∀ q : ℤ, (P.X q).IsFlat) →
    pullSquareFormula
      (f.modulePull A).mapDerivedCategoryFactors.hom
      (ConstantCompletion.extendComparison (ConstantCompletion.quotient U.topology A I n))
      (ConstantCompletion.mapComplexSquare (f.modulePull A)
        (ConstantCompletion.change (ConstantCompletion.quotient U.topology A I n))
        (ConstantCompletion.change (ConstantCompletion.quotient V.topology A I n))
        (f.modulePull (quotientRing A I n))
        (ConstantCompletion.ordinaryFinitePull f.algebra f.direct f.adjunction A I n))
      (ConstantCompletion.extendComparison (ConstantCompletion.quotient V.topology A I n))
      (f.modulePull (quotientRing A I n)).mapDerivedCategoryFactors.hom e P
```

The three additional public predicates are:

```lean
def comparisonSquareFormula
    {C H₁ H₂ H₃ D₀ D₁ D₂ D₃ : Type*}
    [Category C] [Category H₁] [Category H₂] [Category H₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    {q₀ : C ⥤ D₀} {q₁ : H₁ ⥤ D₁} {q₂ : H₂ ⥤ D₂} {q₃ : H₃ ⥤ D₃}
    {r : C ⥤ H₁} {b : C ⥤ H₂} {p : H₁ ⥤ H₃} {s : H₂ ⥤ H₃}
    {dr : D₀ ⥤ D₁} {db : D₀ ⥤ D₂} {dp : D₁ ⥤ D₃} {ds : D₂ ⥤ D₃}
    (α : q₀ ⋙ dr ⟶ r ⋙ q₁) (β : q₁ ⋙ dp ⟶ p ⋙ q₃)
    (γ : r ⋙ p ≅ b ⋙ s) (δ : q₀ ⋙ db ⟶ b ⋙ q₂)
    (ε : q₂ ⋙ ds ⟶ s ⋙ q₃) (e : dr ⋙ dp ≅ db ⋙ ds) (X : C) : Prop :=
  e.hom.app (q₀.obj X) ≫ ds.map (δ.app X) ≫ ε.app (b.obj X) =
    dp.map (α.app X) ≫ β.app (r.obj X) ≫ q₃.map (γ.hom.app X)
```

```lean
def pullSquareFormula
    {C H₁ H₂ H₃ D₀ D₁ D₂ D₃ : Type*}
    [Category C] [Category H₁] [Category H₂] [Category H₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    {q₀ : C ⥤ D₀} {q₁ : H₁ ⥤ D₁} {q₂ : H₂ ⥤ D₂} {q₃ : H₃ ⥤ D₃}
    {r : C ⥤ H₁} {b : C ⥤ H₂} {p : H₁ ⥤ H₃} {s : H₂ ⥤ H₃}
    {dr : D₀ ⥤ D₁} {db : D₀ ⥤ D₂} {dp : D₁ ⥤ D₃} {ds : D₂ ⥤ D₃}
    (α : q₀ ⋙ dr ⟶ r ⋙ q₁) (β : q₁ ⋙ dp ⟶ p ⋙ q₃)
    (γ : r ⋙ p ≅ b ⋙ s) (δ : q₀ ⋙ db ⟶ b ⋙ q₂)
    (ε : q₂ ⋙ ds ⟶ s ⋙ q₃) (e : dr ⋙ dp ≅ db ⋙ ds) (X : C) : Prop :=
  dp.map (α.app X) ≫ β.app (r.obj X) ≫ q₃.map (γ.hom.app X) =
    e.hom.app (q₀.obj X) ≫ ds.map (δ.app X) ≫ ε.app (b.obj X)
```

```lean
def evaluationSquareFormula
    {C H₁ H₂ H₃ D₀ D₁ D₂ D₃ : Type*}
    [Category C] [Category H₁] [Category H₂] [Category H₃]
    [Category D₀] [Category D₁] [Category D₂] [Category D₃]
    {q₀ : C ⥤ D₀} {q₁ : H₁ ⥤ D₁} {q₂ : H₂ ⥤ D₂} {q₃ : H₃ ⥤ D₃}
    {r : C ⥤ H₁} {b : C ⥤ H₂} {p : H₁ ⥤ H₃} {s : H₂ ⥤ H₃}
    {dr : D₀ ⥤ D₁} {db : D₀ ⥤ D₂} {dp : D₁ ⥤ D₃} {ds : D₂ ⥤ D₃}
    (α : q₀ ⋙ dr ⟶ r ⋙ q₁) (β : q₁ ⋙ dp ⟶ p ⋙ q₃)
    (γ : r ⋙ p ≅ b ⋙ s) (δ : q₀ ⋙ db ⟶ b ⋙ q₂)
    (ε : s ⋙ q₃ ≅ q₂ ⋙ ds) (e : dr ⋙ dp ≅ db ⋙ ds) (X : C) : Prop :=
  e.hom.app (q₀.obj X) ≫ ds.map (δ.app X) =
    dp.map (α.app X) ≫ (β.app (r.obj X) ≫ q₃.map (γ.hom.app X)) ≫
      ε.hom.app (b.obj X)
```

The signatures and mathematical meanings of
`Morphism.reductionPullIso_normalized`, `Morphism.finitePullIso_normalized`, and
`Site.finiteEvaluationIso_normalized` are unchanged. Each previously wrote its
representative equation directly. Each now applies a small public predicate
with abstract categories and functors to exactly the same comparisons:

- `comparisonSquareFormula`: the reduction/pullback equation;
- `pullSquareFormula`: the finite-pullback equation, in its original direction;
- `evaluationSquareFormula`: the finite-evaluation equation, including the final
  restriction-factor hom and the original parentheses.

Unfolding these predicates gives the original equations, with only functor
composition and `reductionComplex` aliases expanded. No hypotheses, isomorphism
directions, coefficient rings, choices, or conclusions change.

Proved private wrappers of `ConstantCompletion.resolving_square_iso` expose
these predicates without repeatedly checking concrete tensor expressions. The
evaluation wrapper performs cancellation by `Iso.comp_inv_eq` with abstract
endpoints. The generic wrappers introduce no assumptions or object choices.

The definition node `def-pur-adic-site-strict-quotient-interface` records the
three additional public predicates; all existing attachments and dependencies
are preserved.

## Consumers

The normalized predicates are referenced directly by their existence/uniqueness
theorems in the same module. Two external modules consume their equations through
`exists.choose_spec`: `Sheaf.Paper.ReductionPullFiniteEvaluation` and
`Sheaf.Paper.CompletionUnitFiniteProjection`. The first combined compile checked the item in 45.1 seconds. The original
`CompletionUnitFiniteProjection` failed at its rewrite of
`quotientEvaluationComplexIso_hom_id`: the type of `he` was still headed by
`evaluationSquareFormula`, so the rewrite could not find the component.
Its single necessary adaptation is `dsimp only [evaluationSquareFormula] at he`
immediately after obtaining `he` in `unit_projection_model`. No existing
signature or import changes. Its current holder is unclaimed (no claim lock).
The original `ReductionPullFiniteEvaluation`, compiled against the changed
item, typechecks but exceeds the time limit (78.6 seconds; a profile run took
60.4 seconds, with 24.1 seconds in kernel checking the concrete model
specialization). Its holder is also unclaimed. Added a proved private adapter
`finite_model_abstract_normalized`: it accepts the four existing normalization
hypotheses as abstract predicates and unfolds them only with abstract functors
before applying the existing `finite_model_abstract`. The concrete specialization now calls this adapter. The adapter's hypotheses
unfold to exactly the original equations and add no mathematical assumption.
The first delivery check still reported this consumer over 60 seconds. A private
`finiteCubeFormula` therefore also retains the shape of the derived cube through
the complex, model and transport lemmas. Their private result types expand to precisely the
original equations. A proved private finishing lemma performs the final inverse
cancellation with abstract functors before specialization. The existing private complex-square abbreviations remain unchanged. Redundant local
instances of the global `reductionTower_additive` instance were removed from the model
proof. All public signatures, visibility and imports stay verbatim; no public statement
changes.
Both consumers are therefore included in the delivery and checked against the
changed item. No module held by
another group is edited. No target statement changes, and the
uniquely normalized chosen isomorphisms retain exactly their original meanings.

The current direct importers of the item module are:

- `lean/Sheaf/Paper/CompletionFiniteReduction.lean`
- `lean/Sheaf/Paper/CompletionUnitFiniteProjection.lean`
- `lean/Sheaf/Paper/OrientedNearbyCycles.lean`
- `lean/Sheaf/Paper/PerfectQuotientExchangePresentation.lean`
- `lean/Sheaf/Paper/PerfectReductionProjectionEvaluation.lean`
- `lean/Sheaf/Paper/PerfectStrictReductionProjection.lean`
- `lean/Sheaf/Paper/ProEtaleConstantReductionModels.lean`
- `lean/Sheaf/Paper/ReductionPullFiniteEvaluation.lean`
- `lean/Sheaf/Paper/SfCbcCompactSupportCompositionLimit.lean`
- `lean/Sheaf/Paper/SmallSiteDirectImageReconstruction.lean`
- `lean/Sheaf/Paper/SmallSiteReducedCompletionUnit.lean`
- `lean/Sheaf/Paper/StrictReductionProjectionCompletionUnit.lean`

## Users

The declaration-use scan reports the following modules (including two unrelated
names in the `OrderedExchange` namespace). The transitive import scan has 3347
modules; their statements are unchanged because all three predicate bodies expand
to the original equations and all existing public signatures stay verbatim.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.CompletionMateComparison` | G4 | Three existence proofs filled; normalization bodies folded into abstract predicates. |
| `Sheaf.Paper.CompletionUnitFiniteProjection` | unclaimed | One explicit unfolding before the existing component rewrite. |
| `Sheaf.Paper.ReductionPullFiniteEvaluation` | unclaimed | Private adapters keep the same normalization and cube equations abstract. |
| `Sheaf.Paper.ProEtaleConstantReductionModels` | unclaimed | Textual hit is a different `OrderedExchange.reductionPullIso_existsUnique`; no change. |
| `Sheaf.Paper.SfCbcDirectImageReductionUnit` | unclaimed | Uses that different `OrderedExchange` declaration; no change. |

The target statements retain exactly their original meanings: unfolding each
normalization gives the same maps and equality. This definition change is submitted
for independent review, including the target meaning check, before landing.

## Status

landed 20261026T023225-L-532415 2026-10-26 (merge of deliver/G4/Sheaf.Paper.CompletionMateComparison)

The final item compiles in 32.9 seconds without profiling. The adapted
completion-unit consumer compiles in 47.7 seconds under profiling. The
finite-evaluation consumer compiles in 24.9 seconds under profiling after keeping
the complex and derived cube equations abstract. All profiling options are removed.
Delivery preflight checks the complete packet without profiling; global-build
verification belongs to the maintainer.
