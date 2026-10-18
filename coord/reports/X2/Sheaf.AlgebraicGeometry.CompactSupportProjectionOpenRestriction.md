## What changed

Proved both theorems in `Sheaf.AlgebraicGeometry.CompactSupportProjectionOpenRestriction`
without changing either signature. The forward theorem is the exact specialization of
`compactProjectionMapCoeffFirst_baseChangeMap Λ (IsPullback.of_hasPullback f u) M K`.
The inverse theorem applies congruence to precompose and postcompose the forward identity
with the inverse projection maps, then uses functoriality and isomorphism cancellation.
Updated the existing node's proof, proof dependencies, proof origin and obsolete tool-use entry
to record this proof. No new declarations, definitions or interface changes.

The final single-file compile with the pruned imports succeeded without warnings in
23.5 seconds. The delivery preflight supplies declaration and axiom probes.

## Proved and sorry left

Closed 2 of 2 original holes:

- `AlgebraicGeometry.Etale.compactSupportProjection_open_restriction`
- `AlgebraicGeometry.Etale.compactSupportProjection_open_restriction_inverse`

Both belong to `lem-amb-shriek-projection-open-restriction`. Zero holes remain in the item;
zero holes or split-off statements are added. This proves the item from the existing stated
coefficient-first exchange theorem, whose own proof remains the responsibility of its item.

## No longer needed

Removed these five proof imports:

- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriek`
- `WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`
- `WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`

The corresponding direct proof dependencies are pruned:
`def-amb-etale-compact-support`, `def-weil-pbc-etale-shriek-base-change-map`,
`lem-amb-unbounded-compact-support-comparisons`, `lem-pur-etale-open-derived-tensor`,
and `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
Their normalizations already occur in the definitions and statement of the retained
`lem-asd-compact-projection-exchange`; no separate comparison theorem is applied here.
Removed the obsolete direct tool-use approval for `lem-pur-etale-open-derived-tensor`.
This does not claim these notions or modules are globally unused: some remain transitive
imports of the retained public statement dependencies. Both original public imports stay.
No unit statement or step is bypassed, and no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The DAG's separate refinement-transport step was redundant for the actual Lean statement:
the general theorem already uses precisely the same compactification-independent map names
and tensor/square comparisons. Its inverse step mentioned four projection maps and inverse
exchange maps, whereas the displayed identity needs only the two projection maps assumed
isomorphisms. The proof uses no invertibility assumption on the exchange. The node proof
now records the exact specialization and cancellation argument. No statement repair was needed.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
