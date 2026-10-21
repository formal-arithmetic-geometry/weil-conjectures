# Sheaf.Paper.ConstantWeilStructure

## Reason

Server preflight classifies added section commands, variables, scoped notation and local
attributes as a potential interface change. This record documents those proof-support
commands. No existing public declaration, definition body, public import, global instance
attribute or target statement changes. The three original theorem signatures below are
retained verbatim. All added declarations are private and proved.

The generic helpers introduce universes `c w d r`, private section variables, and
`open scoped ChangeOfRings`. The `ConstantWeilUnitProof` section sets
`backward.isDefEq.respectTransparency.types` to false while elaborating its private
helpers; the section closes before the original public declarations resume. Explicit
local irreducibility attributes keep scalar-extension witnesses, limit constructions and
constructed comparison maps from being expanded during later proof elaboration. They do
not change the definitions. All these attributes are section-local. The two local
heartbeat options affect only their immediately following private proofs; the file's
60-second compile limit is unchanged.

## Old

```lean
theorem constantWeilIntegralComplex_good (Y : Scheme.{u}) :
    integralOperationsGoodComplex l E Y (constantWeilIntegralComplex l E Y)

theorem constantWeilChainUnit_existsUnique {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    ∃! η : constantWeilIntegralComplex l E X ⟶
        (integralOperationsPullbackComplexFunctor l E g).obj
          (constantWeilIntegralComplex l E Y),
      (∀ (n : ℕ) (V : Y.ProEt),
        ((η.f 0 ≫
          (CochainComplex.mappingCocone.fst
            (constantWeilPullbackRoosEndomorphism l E g)).f 0 ≫
          (Pi.π (fun m ↦ (constantWeilPullbackTower l E g).obj (op m)) n).f 0).val.app
            (op ((proEtaleBaseChange g).obj V)))
          (constantWeilUnitSection l E X ((proEtaleBaseChange g).obj V)) =
        integralOperationsPullbackGenerator l E g n
          (((unrestrictedIntegralFiniteComplex l E Y n).obj
            (constantWeilIntegralComplex l E Y)).X 0) V
          (constantWeilReducedUnitSection l E Y n V)) ∧
      (∀ i : ℤ, η.f i ≫
        (CochainComplex.mappingCocone.snd
          (constantWeilPullbackRoosEndomorphism l E g)).v i (i - 1) (by omega) = 0)

theorem constantWeilChainUnit_isIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    IsIso (DerivedCategory.Q.map (constantWeilChainUnit l E g))
```

There were no private proof-support sections at these insertion points.

## New

```lean
theorem constantWeilIntegralComplex_good (Y : Scheme.{u}) :
    integralOperationsGoodComplex l E Y (constantWeilIntegralComplex l E Y)

theorem constantWeilChainUnit_existsUnique {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    ∃! η : constantWeilIntegralComplex l E X ⟶
        (integralOperationsPullbackComplexFunctor l E g).obj
          (constantWeilIntegralComplex l E Y),
      (∀ (n : ℕ) (V : Y.ProEt),
        ((η.f 0 ≫
          (CochainComplex.mappingCocone.fst
            (constantWeilPullbackRoosEndomorphism l E g)).f 0 ≫
          (Pi.π (fun m ↦ (constantWeilPullbackTower l E g).obj (op m)) n).f 0).val.app
            (op ((proEtaleBaseChange g).obj V)))
          (constantWeilUnitSection l E X ((proEtaleBaseChange g).obj V)) =
        integralOperationsPullbackGenerator l E g n
          (((unrestrictedIntegralFiniteComplex l E Y n).obj
            (constantWeilIntegralComplex l E Y)).X 0) V
          (constantWeilReducedUnitSection l E Y n V)) ∧
      (∀ i : ℤ, η.f i ≫
        (CochainComplex.mappingCocone.snd
          (constantWeilPullbackRoosEndomorphism l E g)).v i (i - 1) (by omega) = 0)

theorem constantWeilChainUnit_isIso {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] :
    IsIso (DerivedCategory.Q.map (constantWeilChainUnit l E g))
```

The added proof-support scopes are `ConstantWeilUnitProof`, `ChainConstruction`,
`LevelIsoProof`, `CoefficientTowerProof`, `FinalAssemblyProof` and `NormalizedUnitUse`,
and unnamed sections for the generic scalar-extension and pullback lemmas. Every scope
closes in the same module. For example, the final scope is exactly:

```lean
section NormalizedUnitUse
attribute [local irreducible] unrestrictedIntegralReductionExistence limit
  chainUnitCandidate pullbackUnitProduct pullbackUnitLevel
```

It closes with `end NormalizedUnitUse` immediately after
`constantWeilChainUnit_isIso`. No global reducibility attribute is changed. The two
existing elaboration options, the existing public section, and the existing scoped
instance-removal command are retained.

## Users

`tools/downstream.py Sheaf.Paper.ConstantWeilStructure --uses
constantWeilIntegralComplex_good constantWeilChainUnit_existsUnique
constantWeilChainUnit_isIso` reports the item itself as the sole textual user of each of
the three theorem names. It also lists 114 transitive module importers; none uses the
new private helpers, and all original definitions, theorem signatures and public
imports are unchanged. There are no forced adaptations.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstantWeilStructure | F2 | Three proof holes filled; private proof scopes added; public interface preserved. |

The target statements and the meanings of every definition they use are unchanged.
The independent delivery reader can check the literal old/new signature and definition
comparisons and the scope closures; no second worker was started.

## Status

landed 20261021T203448-L-3769261 2026-10-21 (merge of deliver/F2/Sheaf.Paper.ConstantWeilStructure)
