# AlgebraicGeometry.Scheme.Modules.exteriorSheaf_restrict_iso

## Reason

Retire `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictIso` under its
`coord/retire-items.tsv` row and the human-approved hand-off in
`coord/changes/retire-sheaf-twins-20261020.md`. Its upstream twin is already proved.
The API difference is `exteriorSheaf` versus `exteriorPower`; the existing proved
`exteriorSheaf_eq_exteriorPower` identifies these constructions without hypotheses.
The item already has zero holes, so this is a duplicate retirement, not a hole closure.

## Old

The withdrawn Sheaf module exported:

```lean
theorem exteriorSheaf_restrict_iso {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (U : X.Opens) :
    Nonempty ((exteriorSheaf M n).restrict U.ι ≅ exteriorSheaf (M.restrict U.ι) n)
```

It also repeated private proofs of the presheaf and sheaf comparisons with upstream.

## New

The DAG attachment uses the unchanged, proved upstream declaration:

```lean
theorem exteriorSheaf_restrict_iso {X : Scheme.{v}} (M : X.Modules) (n : ℕ)
    (U : X.Opens) :
    Nonempty ((exteriorPower M n).restrict U.ι ≅ exteriorPower (M.restrict U.ι) n)
```

Every direct consumer privately imports the upstream module and
`Sheaf.AlgebraicGeometry.Modules.ExteriorSheafComparison`. Each obtains the
upstream restriction isomorphism, rewrites both exterior powers by the proved
equality at the module and its restriction, and uses the resulting legacy-object
isomorphism in the original proof. Public signatures, public imports, attributes,
definitions and docstrings of the consumers are unchanged. The five consumer
nodes record that comparison dependency. The restriction node keeps its mathematical
statement and proof route, and now points at the upstream theorem. No upstream file
or target is edited. The item is withdrawn using `deleted.txt`; no DAG node is deleted.

The comparison and restriction theorem require neither local freeness nor positivity.
They therefore cover degree zero, empty opens, empty schemes and zero scalar rings
without any case split. Equality of the exterior constructions also ensures that
no target meaning changes. The blueprint unit route is preserved.

## Users

`tools/downstream.py` lists the sixteen downstream modules below; its declaration-use
scan lists the five direct consumers and the withdrawn item. All downstream modules
are unclaimed at this check. All five adapted files compile individually through
`lcompile.py --all`, and the declaration parser reports no changed public signatures
and zero holes before or after in each. No remaining live or quarantined module
imports the retired module after applying this packet.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictIso | K4 | Withdraw duplicate; attach node to upstream theorem. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtDualExteriorConormal | unclaimed | Replace private import and transport the upstream restriction isomorphism. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtYonedaSurjection | unclaimed | Replace private import and transport the upstream restriction isomorphism. |
| Sheaf.AlgebraicGeometry.Modules.ExteriorSheafFullOpenIso | unclaimed | Replace private import and transport the upstream restriction isomorphism. |
| Sheaf.AlgebraicGeometry.Modules.ExteriorSheafTopInvertible | unclaimed | Replace private import and transport the upstream restriction isomorphism. |
| Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChartFromSections | unclaimed | Replace private import and transport the upstream restriction isomorphism. |
| Sheaf.AlgebraicGeometry.DeterminantDualEvaluation | unclaimed | Transitive; direct consumer signature unchanged; no edit. |
| Sheaf.AlgebraicGeometry.KoszulExtConstantRankTop | unclaimed | Transitive; direct consumer signature unchanged; no edit. |
| Sheaf.AlgebraicGeometry.KoszulSelfExtExterior | unclaimed | Transitive; direct consumer signature unchanged; no edit. |
| Sheaf.AlgebraicGeometry.Modules.DeterminantShortExact | unclaimed | Transitive; direct consumer signature unchanged; no edit. |
| Sheaf.AlgebraicGeometry.SelfTorBasicIdealWedgeCoordinates | unclaimed | Transitive; direct consumer signature unchanged; no edit. |
| Sheaf.AlgebraicGeometry.SelfTorCompatibleAffineMaps | unclaimed | Transitive; direct consumer signature unchanged; no edit. |
| Sheaf.AlgebraicGeometry.SelfTorConormalWedgeChart | unclaimed | Transitive; direct consumer signature unchanged; no edit. |
| Sheaf.AlgebraicGeometry.SelfTorIdealWedgeCoordinates | unclaimed | Transitive; direct consumer signature unchanged; no edit. |
| Sheaf.AlgebraicGeometry.SelfTorLocalWedgeCoordinates | unclaimed | Transitive; direct consumer signature unchanged; no edit. |
| Sheaf.AlgebraicGeometry.SelfTorNestedAffineCoordinates | unclaimed | Transitive; direct consumer signature unchanged; no edit. |
| Sheaf.AlgebraicGeometry.ShiftedDeterminantDualEvaluation | unclaimed | Transitive; direct consumer signature unchanged; no edit. |

## Status

landed 20261020T221234-L-4162476 2026-10-20 (merge of deliver/K4/Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRestrictIso)
