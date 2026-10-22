# TraceFirstAssertion and its canonical comparison data

## Reason

The kernel repeatedly compares concrete derived monoidal instances after
`Lean.Meta.abstractNestedProofs` replaces proof arguments inside definition
values. The declared types retain the original proof arguments. The resulting
proof-irrelevance comparisons recursively compare large propositions containing
further instances. The implementation notes of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs`, lines 109–152,
describe this same issue and its solution using a tensor-structure bundle.

Store the canonical data once and use projections from the same bundle in the
formula. No map, tensor, symmetry, adjunction or mathematical hypothesis changes.
No data is selected from an existence theorem.

## Old

The old assertion is:

```lean
def TraceFirstAssertion {X Y W : Scheme.{u}} (f : X ⟶ Y) (p q : W ⟶ X)
    (sq : ChosenCartesianSquare p q f f) (TY : TraceD Λ Y) : Prop :=
  TraceFirstFormula (TraceLoc Λ Y) (TraceLoc Λ X) (TraceLoc Λ W)
    (tracePull Λ f) (tracePush Λ f)
    (tracePull Λ p) (tracePull Λ q)
    (tracePush Λ p) (tracePush Λ q)
    (traceAdjunction Λ f)
    (traceAdjunction Λ p) (traceAdjunction Λ q)
    (tracePullSquare Λ f p q sq.w)
    (condensedDerivedUnitIso Λ f)
    (traceTensorComponent (tracePull Λ f)
      (condensedDerivedTensorComparison Λ f))
    (traceTensorComponent (tracePull Λ p)
      (condensedDerivedTensorComparison Λ p))
    (traceTensorComponent (tracePull Λ q)
      (condensedDerivedTensorComparison Λ q))
    (condensedDerivedSymmetry Λ X) (condensedDerivedSymmetry Λ W) TY
```

`condensedDerivedUnitIso` used the explicit degree-zero composite through
`leftDerivedUpperStarIsoMapDerivedCategory`, `mapDerivedCategoryFactors` and
`DerivedCategory.Q.mapIso` of the ordinary unit isomorphism.
`condensedDerivedSymmetry` was the canonical
`DerivedMonoidal.braiding' DerivedCategory.Qh` construction. The unused
`condensedDerivedTensorIso` was
`asIso (upperStar Λ f).leftDerivedTensorComparison`.

## New

The assertion uses the same displayed formula through the stored data:

```lean
def TraceFirstAssertion {X Y W : Scheme.{u}} (f : X ⟶ Y) (p q : W ⟶ X)
    (sq : ChosenCartesianSquare p q f f) (TY : TraceD Λ Y) : Prop :=
  traceDataFormula (traceNativeComparisonData Λ f p q)
    (TraceLoc Λ Y) (TraceLoc Λ X) (TraceLoc Λ W)
    (tracePush Λ f) (tracePush Λ p) (tracePush Λ q)
    (traceAdjunction Λ f) (traceAdjunction Λ p) (traceAdjunction Λ q)
    (tracePullSquare Λ f p q sq.w) TY
```

The bundle has only the following existing data:

```lean
structure TraceComparisonData
    {C : Type u₁} {D : Type u₂} {V : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} V]
    (F : C ⥤ D) (U₁ U₂ : D ⥤ V) where
  /-- The tensor structure in the source category. -/
  [monoidalC : MonoidalCategory C]
  /-- The tensor structure in the middle category. -/
  [monoidalD : MonoidalCategory D]
  /-- The tensor structure in the final category. -/
  [monoidalV : MonoidalCategory V]
  /-- The specified unit comparison. -/
  unitIso : F.obj (𝟙_ C) ≅ 𝟙_ D
  /-- The tensor comparison for the first functor. -/
  tensorF : ∀ K M : C, F.obj (K ⊗ M) ⟶ F.obj K ⊗ F.obj M
  /-- The tensor comparison for the first branch. -/
  tensorOne : ∀ K M : D, U₁.obj (K ⊗ M) ⟶ U₁.obj K ⊗ U₁.obj M
  /-- The tensor comparison for the second branch. -/
  tensorTwo : ∀ K M : D, U₂.obj (K ⊗ M) ⟶ U₂.obj K ⊗ U₂.obj M
  /-- The specified symmetry in the middle category. -/
  symmetryD : ∀ K M : D, K ⊗ M ≅ M ⊗ K
  /-- The specified symmetry in the final category. -/
  symmetryV : ∀ K M : V, K ⊗ M ≅ M ⊗ K
```

Its generic constructor explicitly supplies the existing maps:

```lean
def derivedTraceComparisonData :
    TraceComparisonData F.leftDerivedFunctor U₁.leftDerivedFunctor U₂.leftDerivedFunctor where
  unitIso := F.traceDegreeZeroUnitIso
  tensorF K M := (F.leftDerivedTensorComparison.app K).app M
  tensorOne K M := (U₁.leftDerivedTensorComparison.app K).app M
  tensorTwo K M := (U₂.leftDerivedTensorComparison.app K).app M
  symmetryD := CategoryTheory.traceCanonicalDerivedBraiding
  symmetryV := CategoryTheory.traceCanonicalDerivedBraiding
```

The wrapper merely installs the three stored tensor structures and calls the
unchanged formula:

```lean
def traceDataFormula
    {C : Type u₁} {D : Type u₂} {V : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} V]
    {F : C ⥤ D} {U₁ U₂ : D ⥤ V} (T : TraceComparisonData F U₁ U₂)
    (LC : ObjectProperty C) (LD : ObjectProperty D) (LV : ObjectProperty V)
    (P : D ⥤ C) (Q₁ Q₂ : V ⥤ D)
    (a : F ⊣ P) (a₁ : U₁ ⊣ Q₁) (a₂ : U₂ ⊣ Q₂)
    (s : F ⋙ U₂ ≅ F ⋙ U₁) (TY : C) : Prop :=
  letI := T.monoidalC
  letI := T.monoidalD
  letI := T.monoidalV
  TraceFirstFormula LC LD LV F P U₁ U₂ Q₁ Q₂ a a₁ a₂ s
    T.unitIso T.tensorF T.tensorOne T.tensorTwo T.symmetryD T.symmetryV TY
```

`moduleTraceComparisonData` specializes this constructor to `Mod C R` over
abstract ambient categories. `traceNativeComparisonData` specializes it to the
three recorded pullbacks. Thus the fields reduce to the former unit, tensor and
Koszul comparisons, with the same ordinary chosen monoidal structures.
The generic braiding cache is exactly
`(DerivedCategory.braidedCategory' A).braiding`. The generic unit cache contains
verbatim the old explicit degree-zero composite; `derived_unit_explicit` and
`derived_unit_monoidal_explicit` prove its two canonical unit identifications.
No inverse or comparison is chosen from a mere existence statement.

The public ordinary sheaf cache `CategoryTheory.traceSheafSymmetric` is a record
update of `Sheaf.symmetricCategory J A` with parent
`Sheaf.braidedCategory J A`. Its generic reflexivity theorem checks equality
with the original structure. Its registration is local to this module. Derived symmetry is proved from the existing symmetry law. The derived braided
functor instances are constructed locally inside the abstract assembly proof;
no extra data factory is specialized at the concrete sheaf categories.

The unused native `condensedDerivedSymmetry` alias is removed: the assertion now
uses the identical braiding through the bundle. The unused
`condensedDerivedTensorIso` alias is removed. All three declarations have no external
consumer in the source roots, quarantine, DAG proof steps or unit records, and
their Lean attachments are removed. The unused native tensor-comparison alias is also removed. The square calculation
is proved generically from the canonical comparison, then specialized through the
private folded proposition traceDataSquare over the same stored bundle. This
private proof predicate changes no public statement or map. A fresh whole
source/quarantine/DAG scan found no external consumer. The public unit alias used
by TraceBaseChangeSecond remains available. No source-library declaration is removed.

## Users

The source-only downstream scan found 74 downstream modules. All direct public
name uses and the preserved sources of the two quarantined consumers were read.
Their rework records and Lean attachments are retained. None of the three removed aliases has an external user.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.TraceBaseChangeFirst | V9 | same formula and canonical maps through bundle fields |
| Sheaf.Paper.ProEtaleProjectionExchangeMaps | unclaimed | public functor and adjunction aliases unchanged |
| Sheaf.Paper.TraceBaseChangeSecond | unclaimed | same explicit unit composite; other used aliases unchanged |

No consumer adaptation is required. All three theorem signatures are unchanged.
Targets using the changed definition are submitted for statement review again;
the explicit constructor fields and wrapper preserve the old mathematical
formula and every hypothesis.

## Status

landed 20261022T013535-L-3614540 2026-10-22 (merge of deliver/V9/Sheaf.Paper.TraceBaseChangeFirst)
