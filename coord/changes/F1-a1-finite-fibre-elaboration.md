# a1FiniteFibreBaseChange and finite-fibre geometry instances

## Reason

Restore the quarantined module recorded in coord/rework.tsv, preserving its Lean
attachment and all 42 original declarations. The original timeout was reproduced during
profiling. A clean baseline took 42.8 seconds, with profiling attributing 24.1 seconds to
instance inference. The finite fibre's locally-finite-type and quasi-compact structures
were repeatedly reconstructed from its finite structure. Cache those inherited instances.
The long counit-mate definition was also transparent in later IsIso and equivariance
statements: mark it irreducible, retaining its literal body and mathematical value.

This is a reducibility and elaboration repair. No target statement changes; no
mathematical definition or theorem statement changes. The added instances are proofs
of propositions already inferred by Lean. Their values are equal by proof irrelevance.
The consumer's unfinished proof does not unfold the mate, and requires no adaptation.

The added file-local `set_option linter.unusedSectionVars false` preserves the original
section binders of the now-proved preliminary theorems. It suppresses only unused-section-
variable style warnings, and changes no proof or importer environment. The private
`property_of_factorization` helper proves the generic full-subcategory factorization
argument; it is absent from all public signatures and data definitions.
The chosen common-stage pullback and standard t-structure are kept locally irreducible
from this helper onward. These attributes are local and do not escape the module.

## Old

```lean
def a1FiniteFibreBaseChange (F : sfCommonStageWeilComplex D l hl X₀ Ω) :
    (a1FiniteFibreStalkPair D g₀ y ι hι l hl Ω F).carrier ⟶
      ((sfModelWeilDerivedPush (a1ResidueDatum D Y₀ y ι hι) l hl Ω
        (a1FiniteFibreStructure D g₀ y ι hι)).obj
          (a1FiniteFibreWeilComplex D g₀ y ι hι l hl Ω F)).carrier :=
  let B := a1ResidueDatum D Y₀ y ι hι
  let a := a1FiniteFibreStructure D g₀ y ι hι
  let i := a1FiniteFibreInclusion D g₀ y ι hι
  let t := a1FiniteFibrePointInclusion D y ι hι
  let P := (sfModelWeilDerivedPush D l hl Ω g₀).obj F
  let G := a1FiniteFibreWeilComplex D g₀ y ι hι l hl Ω F
  letI := sfWeilPrimeInvertible B l hl (a1FiniteFibreModel D g₀ y)
  letI := sfWeilPrimeInvertible B l hl (sfWeilCohomologyPoint B)
  letI := sfWeilPrimeInvertible D l hl X₀
  letI := sfWeilPrimeInvertible D l hl Y₀
  (sfModelDerivedAdjunction B l hl Ω a).homEquiv _ _
    (((zlPullComp l Ω (zlFiberMap B a) t).app P.carrier).inv ≫
      eqToHom (congrArg (fun f ↦ (commonStageDerivedPullback l Ω f).obj P.carrier)
        (a1FiniteFibreSquare D g₀ y ι hι)) ≫
      ((zlPullComp l Ω i (zlFiberMap D g₀)).app P.carrier).hom ≫
      (commonStageDerivedPullback l Ω i).map (a1FiniteFibreCounit D g₀ l hl Ω F)) ≫
    (sfModelWeilDerivedPushForget B l hl Ω a).inv.app G
```

The two named finite-type/quasi-compact instances were absent. They were synthesized
through a1FiniteFibreModel_finite and the standard finite-morphism instances.

## New

The new private helper is fully proved:

```lean
private theorem property_of_factorization
    {C : Type*} [Category* C] {B : Type*} [Category* B]
    {P : ObjectProperty C} {Q : ObjectProperty B} {H : C ⥤ B}
    (G : P.FullSubcategory ⥤ Q.FullSubcategory) (h : G ⋙ Q.ι = P.ι ⋙ H)
    (K : P.FullSubcategory) : Q (H.obj K.obj) := by
  have he : (G.obj K).obj = H.obj K.obj :=
    congrArg (fun J : P.FullSubcategory ⥤ B ↦ J.obj K) h
  exact he ▸ (G.obj K).property
```

This helper was absent in the archived source.


The existing option block additionally has:

```lean
set_option linter.unusedSectionVars false
```

The original block did not set this option. All other original options remain unchanged.
Before the private factorization helper the following local attribute command is added:

```lean
attribute [local irreducible] commonStageDerivedPullback sfCommonStageStandardTStructure
```

There was no corresponding command in the archived source. This only controls proof
elaboration in this file and changes no imported declaration's global reducibility.


```lean
@[irreducible]
def a1FiniteFibreBaseChange (F : sfCommonStageWeilComplex D l hl X₀ Ω) :
    (a1FiniteFibreStalkPair D g₀ y ι hι l hl Ω F).carrier ⟶
      ((sfModelWeilDerivedPush (a1ResidueDatum D Y₀ y ι hι) l hl Ω
        (a1FiniteFibreStructure D g₀ y ι hι)).obj
          (a1FiniteFibreWeilComplex D g₀ y ι hι l hl Ω F)).carrier :=
  let B := a1ResidueDatum D Y₀ y ι hι
  let a := a1FiniteFibreStructure D g₀ y ι hι
  let i := a1FiniteFibreInclusion D g₀ y ι hι
  let t := a1FiniteFibrePointInclusion D y ι hι
  let P := (sfModelWeilDerivedPush D l hl Ω g₀).obj F
  let G := a1FiniteFibreWeilComplex D g₀ y ι hι l hl Ω F
  letI := sfWeilPrimeInvertible B l hl (a1FiniteFibreModel D g₀ y)
  letI := sfWeilPrimeInvertible B l hl (sfWeilCohomologyPoint B)
  letI := sfWeilPrimeInvertible D l hl X₀
  letI := sfWeilPrimeInvertible D l hl Y₀
  (sfModelDerivedAdjunction B l hl Ω a).homEquiv _ _
    (((zlPullComp l Ω (zlFiberMap B a) t).app P.carrier).inv ≫
      eqToHom (congrArg (fun f ↦ (commonStageDerivedPullback l Ω f).obj P.carrier)
        (a1FiniteFibreSquare D g₀ y ι hι)) ≫
      ((zlPullComp l Ω i (zlFiberMap D g₀)).app P.carrier).hom ≫
      (commonStageDerivedPullback l Ω i).map (a1FiniteFibreCounit D g₀ l hl Ω F)) ≫
    (sfModelWeilDerivedPushForget B l hl Ω a).inv.app G
```

```lean
instance a1FiniteFibreModel_locallyOfFiniteType :
    LocallyOfFiniteType (a1FiniteFibreModel D g₀ y).hom :=
  inferInstanceAs (LocallyOfFiniteType
    (pullback.snd g₀.left (Y₀.left.fromSpecResidueField y.val)))

/-- Cache quasi-compactness of the finite fibre's structure map.
Source: finite morphisms are quasi-compact
(blueprint: lem-a1-finite-etale-weil-fibre-comparison). -/
instance a1FiniteFibreModel_quasiCompact :
    QuasiCompact (a1FiniteFibreModel D g₀ y).hom :=
  inferInstanceAs (QuasiCompact
    (pullback.snd g₀.left (Y₀.left.fromSpecResidueField y.val)))
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.A1FiniteEtaleWeilFibreComparison | F1 | Restored; same definitions, faster inference and controlled mate unfolding. |
| Sheaf.DeligneLaumon.Reduction.FiniteMapPurity | quarantined, not adapted | Only imports this module; original statement and proof remain valid without unfolding the mate. |

The ordinary downstream script reports the module as unknown because it is quarantined.
A source import-graph scan of both lean/ and quarantine/, with live files taking precedence,
finds exactly the listed consumer and no further transitive importers. DAG parent
lem-a1-finite-map-purity has the same attachment. The archived consumer was read in full.

The final complete module compiled through lcompile.py in 58.2 s, exit code 0,
without warnings. The original 17 theorem holes are reduced to 8, with none added.

## Status

landed 20261024T185116-L-3401258 2026-10-24 (merge of deliver/F1/Sheaf.Paper.A1FiniteEtaleWeilFibreComparison)
