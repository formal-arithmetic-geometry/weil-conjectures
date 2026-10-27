# AlgebraicGeometry.ProEtale.CondensedRing.FiniteEtaleTraceFormula

## Reason

Kernel checking conversion from chart-indexed equations to raw splitting
quantifiers repeatedly unfolds large dependent scheme and module expressions.
The epimorphy-only diagnostic passes; adding that conversion causes a deterministic
kernel timeout, even after sharing the sum. Bundle exactly the old splitting
arguments in `FiniteEtaleModuleChart`, and make the predicate and generic descent
use that same chart type and the same real sum construction.

A chart has exactly the former quantified data: Y, g, a WeaklyEtale proof, n,
the list t, the equations w, and the Nonempty coproduct-splitting certificate.
The structure constructor and projections pack and unpack all those data.
Thus quantification is over exactly the old data, including degree zero and
empty bases. No hypothesis, scheme map, counit, normalization or empty-chart
behavior changes. The outer declaration signature and public imports stay verbatim.

`finiteEtaleTraceSheetComparison_exists` is proved by the original canonical
isomorphism and reflexivity. The definition chooses that uniquely fixed value;
`finiteEtaleTraceSheetComparison_eq` proves equality to exactly `eqToIso.symm`
followed by `upperStarComp`. No data come from an unproved theorem. The shared
`finiteEtaleTraceSheetSum` explicitly sums the actual counit projections using
that comparison. `finiteEtaleSheetSum` merely adapts a chart to its arguments.

Targets using this definition transitively are submitted for renewed semantic
review. The exact field list, real sum body and proved comparison equation
certify that their mathematical meaning has not changed.

Local irreducibility attributes for upperStar, lowerStar, upperStarComp and the
adjunction guide elaboration; no global attribute of an existing declaration changes.

## Old

```lean
def FiniteEtaleTraceFormula
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (τ : (lowerStar Λ p).obj ((upperStar Λ p).obj P) ⟶ P) : Prop :=
  ∀ (Y : Scheme.{u}) (g : Y ⟶ X) [WeaklyEtale g] (n : ℕ)
    (t : Fin n → (Y ⟶ U)) (w : ∀ j, t j ≫ p = g),
    Nonempty (IsColimit (Cofan.mk (pullback p g)
      (fun j ↦ pullback.lift (t j) (𝟙 Y) (by simpa using w j)))) →
    (upperStar Λ g).map τ = ∑ j : Fin n,
      ((eqToIso (congrArg (upperStar Λ) (w j))).symm ≪≫
        upperStarComp Λ (t j) p).hom.app
          ((lowerStar Λ p).obj ((upperStar Λ p).obj P)) ≫
      (upperStar Λ (t j)).map
        ((upperStarLowerStarAdjunction Λ p).counit.app ((upperStar Λ p).obj P)) ≫
      ((eqToIso (congrArg (upperStar Λ) (w j))).symm ≪≫
        upperStarComp Λ (t j) p).inv.app P
```

## New

```lean
/-- A finite splitting chart, allowing the empty splitting.
Source: Stacks Project, Tag 04HN.
(blueprint: def-sfb-internal-finite-etale-trace-formula) -/
structure FiniteEtaleModuleChart {X U : Scheme.{u}} (p : U ⟶ X) where
  base : Scheme.{u}
  map : base ⟶ X
  weaklyEtale : WeaklyEtale map
  degree : ℕ
  sheet : Fin degree → (base ⟶ U)
  over : ∀ j, sheet j ≫ p = map
  splits : Nonempty (IsColimit (Cofan.mk (pullback p map)
    (fun j ↦ pullback.lift (sheet j) (𝟙 base) (by simpa using over j))))

attribute [instance] FiniteEtaleModuleChart.weaklyEtale

/-- The canonical sheet comparison has a uniquely specified value.
Source: the inverse-image composition comparison.
(blueprint: def-sfb-internal-finite-etale-trace-formula) -/
theorem finiteEtaleTraceSheetComparison_exists
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Y : Scheme.{u}} (p : U ⟶ X)
    (g : Y ⟶ X) (t : Y ⟶ U) (w : t ≫ p = g) :
    ∃ a : upperStar Λ g ≅ upperStar Λ p ⋙ upperStar Λ t,
      a = (eqToIso (congrArg (upperStar Λ) w)).symm ≪≫ upperStarComp Λ t p := by
  exact ⟨_, rfl⟩

/-- The canonical sheet comparison, frozen using its proved singleton specification.
Its exact equation below fixes all its components. This avoids kernel reduction
through the large composite adjunction when components are compared.
Source: the inverse-image composition comparison.
(blueprint: def-sfb-internal-finite-etale-trace-formula) -/
@[irreducible]
def finiteEtaleTraceSheetComparison
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Y : Scheme.{u}} (p : U ⟶ X)
    (g : Y ⟶ X) (t : Y ⟶ U) (w : t ≫ p = g) :
    upperStar Λ g ≅ upperStar Λ p ⋙ upperStar Λ t :=
  Classical.choose (finiteEtaleTraceSheetComparison_exists Λ p g t w)

/-- The frozen comparison is exactly the original canonical composition comparison.
Source: the proved specification above.
(blueprint: def-sfb-internal-finite-etale-trace-formula) -/
theorem finiteEtaleTraceSheetComparison_eq
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Y : Scheme.{u}} (p : U ⟶ X)
    (g : Y ⟶ X) (t : Y ⟶ U) (w : t ≫ p = g) :
    finiteEtaleTraceSheetComparison Λ p g t w =
      (eqToIso (congrArg (upperStar Λ) w)).symm ≪≫ upperStarComp Λ t p := by
  unfold finiteEtaleTraceSheetComparison
  exact Classical.choose_spec (finiteEtaleTraceSheetComparison_exists Λ p g t w)

/-- The actual sum of the normalized counit projections on a finite list of sheets.
Source: blueprint, stratified lattice proof, local computation.
(blueprint: def-sfb-internal-finite-etale-trace-formula) -/
@[irreducible]
def finiteEtaleTraceSheetSum
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U Y : Scheme.{u}} (p : U ⟶ X)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (g : Y ⟶ X) (n : ℕ) (t : Fin n → (Y ⟶ U)) (w : ∀ j, t j ≫ p = g) :
    (upperStar Λ g).obj ((lowerStar Λ p).obj ((upperStar Λ p).obj P)) ⟶
      (upperStar Λ g).obj P :=
  ∑ j : Fin n,
    (finiteEtaleTraceSheetComparison Λ p g (t j) (w j)).hom.app
        ((lowerStar Λ p).obj ((upperStar Λ p).obj P)) ≫
      (upperStar Λ (t j)).map
        ((upperStarLowerStarAdjunction Λ p).counit.app ((upperStar Λ p).obj P)) ≫
      (finiteEtaleTraceSheetComparison Λ p g (t j) (w j)).inv.app P

/-- The trace becomes the sum of canonical sheet projections on every split chart.
Each projection is formed from the pullback composition comparison and the actual
pullback/direct-image counit; thus this condition fixes the normalization of trace.
Source: blueprint, stratified lattice proof, "Pushing down by the trace".
(blueprint: def-sfb-internal-finite-etale-trace-formula) -/
def FiniteEtaleTraceFormula
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X U : Scheme.{u}} (p : U ⟶ X)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (τ : (lowerStar Λ p).obj ((upperStar Λ p).obj P) ⟶ P) : Prop :=
  ∀ c : FiniteEtaleModuleChart p,
    (upperStar Λ c.map).map τ =
      finiteEtaleTraceSheetSum Λ p P c.map c.degree c.sheet c.over
```

## Users

`tools/downstream.py Sheaf.Paper.FiniteEtaleTraceFormula --uses
FiniteEtaleTraceFormula` lists these three declaration users (the wider import
closure has 3310 modules). Claims were read on 2026-10-26.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteEtaleTraceFormula | unclaimed | Exact canonical comparisons via the proved equation. |
| Sheaf.Paper.ContinuousFiniteEtaleTrace | M9 | Use the shared comparisons to check normalization. |
| Sheaf.Paper.ContinuousFiniteEtaleTraceImageCharts | U6 | Unchanged hypothesis; compile original against new definition. |

The unchanged U6 consumer compiled in 43.0 seconds against the final structured
predicate (`lcompile.py --all`, result `28e8dcdf24b747f3b147d227`).

No signature or mathematical assertion of a user changes. The U6 module is
copied unchanged solely for validation and is excluded from the delivery.
There are no forced adaptations of another group's module.

## Status

landed 20261026T070326-L-3543209 2026-10-26 (merge of deliver/M9/Sheaf.Paper.ContinuousFiniteEtaleTrace)
