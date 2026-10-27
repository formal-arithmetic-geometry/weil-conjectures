# WeilConjectures.AdicCompactificationSections.commonPull

## Reason

Restore the quarantined zero-hole module from the path recorded in coord/rework.tsv.
The recorded failure was a 60-second timeout. On the current published dependencies the
unchanged archived source compiles in 18.4 seconds. Profiling nevertheless identifies
repeated field-instance search during CommonOpen elaboration: cumulative typeclass
inference was 6.7 seconds. Giving the existing Shrink.instField local priority reduces
this to 1.26 seconds (profiled file compile: 15.2 seconds). This chooses the same existing
field structure on the literal small coefficient model; it constructs no new field.

In addition, expose the pullback's functor type explicitly and mark its implementation
irreducible, so elaboration of comparison data can use that type without entering the
large existsUnique specification used to construct the actual common-stage functor.
The proved equation commonPull_eq supplies its complete original implementation.

## Old

```lean
def commonPull {U T : Geometry D} (j : U.scheme ⟶ T.scheme) :=
  letI := smoothQbarResidueInvertible D l hl U.scheme
  letI := smoothQbarResidueInvertible D l hl T.scheme
  commonStageDerivedPullback l Ω j
```

The instance search used the imported default priority of Shrink.instField.

## New

```lean
attribute [local instance 2000] Shrink.instField

@[irreducible]
def commonPull {U T : Geometry D} (j : U.scheme ⟶ T.scheme) :
    generalAlgebraicallyClosedConstructibleCategory l Ω T.scheme ⥤
      generalAlgebraicallyClosedConstructibleCategory l Ω U.scheme :=
  letI := smoothQbarResidueInvertible D l hl U.scheme
  letI := smoothQbarResidueInvertible D l hl T.scheme
  commonStageDerivedPullback l Ω j
```

The new public theorem commonPull_eq states the equality of commonPull with the complete
old body; its proof is `unfold commonPull; rfl`. Every CommonOpen field, its constructor,
its exported instances, commonRestrictionHom and the public import remain unchanged.
The new local instance priority is confined to this module and is not exported.
There is no mathematical change to any target definition, hypothesis or conclusion;
the definition review for targets remains valid.

## Users

`tools/downstream.py Sheaf.Paper.CommonAdicOpenSectionData --allow-missing --uses
CommonOpen commonPull commonRestrictionHom` finds no live consumers, because this
module is quarantined. An additional import-closure scan of both lean/ and quarantine/
finds the two archived consumers below. No source-tree module is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed, quarantined | Direct consumer of CommonOpen and commonRestrictionHom. Existing fields and formulas unchanged; original source checked against repair. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed, quarantined | Transitive consumer through the comparison-data module. No commonPull unfolding or direct reference to the three changed-module declarations; no adaptation required. |

No consumer currently unfolds commonPull; a future proof can use commonPull_eq.
The archived consumers and their DAG dependencies are retained, not withdrawn.

## Status

landed 20261024T035936-L-1179471 2026-10-24 (merge of deliver/E4/Sheaf.Paper.CommonAdicOpenSectionData)
