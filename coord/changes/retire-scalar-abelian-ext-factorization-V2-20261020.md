# AlgebraicGeometry.Scheme.scalar_unit_abelian_ext_factorization

## Reason

Human-authorized retirement of the duplicate Sheaf module; see the Hand-off in
`coord/changes/retire-sheaf-twins-20261020.md`. The current official twin has the
same public statements, definitions and complete proof, including A2's
`ExtExactFunctorIdentityComparison` import and `exactFunctorIdentityComparison`
proof. Only attribution and a local instance name/line wrapping differ.

Repair of return C-15179 (`15179a969e`): remove the proposed restoration of the
duplicate Sheaf pullback square. Its official twin already contains the same
full names. Repoint its node to the official twin using the requested note,
and preserve the archive without adding its absent path to `deleted.txt`.

## Old

Module: `Sheaf.AlgebraicGeometry.ScalarAbelianExtFactorization`.
The node attaches to that module and its corresponding Lean path.

```lean
theorem scalar_unit_abelian_ext_factorization (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (x : scalarCohomology f (SheafOfModules.unit X.ringCatSheaf) 1) :
    scalarUnitAbelianComparison X x =
      scalarAbelianExtComparison k X (scalarSheaf f (SheafOfModules.unit X.ringCatSheaf)) 1
        (scalarCohomologyExtEquiv f (SheafOfModules.unit X.ringCatSheaf) 1 x)
```

## New

Module: `WeilConjectures.AlgebraicGeometry.ScalarAbelianExtFactorization`.
The signature above is unchanged in the official twin, as are the definitions
`scalarAbelianForget`, `scalarAbelianUnitClass`, `scalarAbelianExtComparison`.
The duplicate file is withdrawn, and the node attaches to the official module.
No upstream source or target statement is modified. No new holes are introduced.

## Users

A current search of `lean/` finds no active importers of the retired copy.
The quarantined pullback-square archive remains historical source; this packet
adds no active copy. The official consumers already import the official
factorization. All parent mathematical dependencies remain unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ScalarAbelianPullbackSquare | unclaimed (quarantined; retire item 1492) | Do not restore the duplicate. Repoint its node to WeilConjectures.AlgebraicGeometry.ScalarAbelianPullbackSquare, set existing=true and record the reviewer-requested retirement note. Same statement and declaration name; official proof unchanged. Archive untouched; absent active path not listed in deleted.txt. |
| Sheaf.AlgebraicGeometry.ScalarForgetPullbackAdjunction | already retired | Official replacement already uses twin; no edit. |
| Sheaf.AlgebraicGeometry.ScalarForgetPullbackComparison | already retired | Official replacement already uses twin; no edit. |
| Sheaf.AlgebraicGeometry.ScalarStructureCoefficientAdjunct | already retired | Official replacement already uses twin; no edit. |

The archive's original import loaded scalarAbelianForget from the Sheaf copy,
then its upstream proof imports loaded the same name from the official twin.
`coord/rework.tsv` records that duplicate-name error. Restoring the archived
module under its Sheaf name would retain duplicate declarations. Using the
existing official module preserves its complete construction and proof.

Only the factorization item is withdrawn in `deleted.txt`. The pullback node's
statement, proof and dependencies remain unchanged. Neither quarantine nor the
source-library tree is modified. Current official modules are validated from
unchanged scratchpad copies through lcompile.py. The factorization, pullback
square, forget-pullback adjunction, forget-pullback comparison and
structure-coefficient adjunct all passed (exit code 0; no warnings).

## Status

landed 20261020T164229-L-3891259 2026-10-20 (merge of deliver/V2/Sheaf.AlgebraicGeometry.ScalarAbelianExtFactorization)
