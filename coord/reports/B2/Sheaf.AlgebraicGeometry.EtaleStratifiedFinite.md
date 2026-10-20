## What changed

Retire the listed zero-hole duplicate `Sheaf.AlgebraicGeometry.EtaleStratifiedFinite`.
Its adopted-source twin `WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite` is
byte-identical from the `module` header, including all imports, declarations and proofs.
The existing upstream theorem supplies the full replacement argument unchanged.
Redirect the sole private import in each of `FrobeniusVectorBundleKernel`,
`NoetherianAffineFreePresentation`, `NoetherianConstructibleGaloisPartition`,
`NoetherianEtaleSumConstructible`, and `CoherentSetCriterion`. In `NoetherianAffineFreePresentation` and `NoetherianEtaleSumConstructible`, also remove
the unused private import `Sheaf.AlgebraicGeometry.FiniteEtalePushforwardFiniteType`,
which server preflight identified as a route-pivot dropped module.

Reattach `lem-weil-pbc-etale-stratified-finite` to the upstream module and file, retaining
its declaration name, statement, proof, dependencies and unit. Withdraw the duplicate
using `deleted.txt`. No adopted-source file is changed.
Change record: `coord/changes/B2-retire-etale-stratified-finite.md`.

Validation: exact-statement example against the upstream theorem compiled, and its
axioms are exactly `propext`, `Classical.choice`, `Quot.sound`.
The five live consumers are compiled individually through `lcompile.py`.

## Proved and sorry left

This is a retirement repair: proved 0 of 0 item sorries; 0 holes closed, 0 holes added,
0 split off. `AlgebraicGeometry.Scheme.exists_etale_stratified_finite` already has a
complete proof, retained in its upstream module. The withdrawn module has zero holes.

The four existing consumer holes are unchanged:

- `AlgebraicGeometry.Scheme.exists_noetherian_affine_free_presentation`
  (`lem-per-noetherian-affine-free-presentation`).
- `AlgebraicGeometry.Etale.exists_noetherian_constructible_galois_partition`
  (`lem-per-noetherian-constructible-galois-partition`).
- `AlgebraicGeometry.Scheme.exists_noetherian_etale_sum_constructible`
  (`lem-per-noetherian-etale-sum-constructible`).
- `AlgebraicGeometry.coherent_iff_finite_constructible_strata`
  (`lem-trf-coherent-set-criterion`).

`FrobeniusVectorBundleKernel` has no holes. No new declaration or node is introduced.

## No longer needed

Also remove two unused import edges to
`Sheaf.AlgebraicGeometry.FiniteEtalePushforwardFiniteType`, one in each of
`NoetherianAffineFreePresentation` and `NoetherianEtaleSumConstructible`. No declaration
in either file uses that theorem; both existing theorem bodies remain `sorry`. This does
not claim that the mathematical lemma in their proof plans has been proved or bypassed.
Its node, statement and existing module remain untouched.

The duplicate module `Sheaf.AlgebraicGeometry.EtaleStratifiedFinite` and its five
live private import edges are removed. Each edge is replaced by the upstream twin.
No mathematical node or proof dependency is pruned: the complete identical upstream
proof still uses the affine-cover stratification, separated stratification, assembly,
local gluing, finite affine covers and pullback pasting. The node and all twelve actual
DAG parent dependencies remain valid through the updated attachment.

The five quarantined historical consumers were inspected, including their rework rows:
`TopologicalStratifiedLisseLattices`, `ContinuousLissePullbackSystem`,
`ContinuousLisseStratifiedLattices`, `LisseEConstructibleIntegralLattice`, and
`StratifiedLattice`. Their archives, dependencies and attachments are preserved.
Their restoration should migrate the old private import to the upstream module;
this packet does not treat their absent live paths as withdrawals or restore them.
All parent names and the full downstream user inventory are recorded in the change record.
The sk-thm-p1 unit's statement and realized route are unchanged.

## Where the brief, the DAG or earlier work was wrong

The first server preflight refused the two pre-existing imports of
`FiniteEtalePushforwardFiniteType`, listed in `coord/route-pivot-dropped-modules.txt`.
They were unused by current Lean declarations; removing them preserves every existing
statement and body and repairs the preflight findings.

The generic proving brief did not mention that this queue item is a listed retirement
repair with zero holes. The existing source duplicate already supplies the complete proof;
rewriting it or claiming a hole closure would misstate the work. The node still attached
the theorem to the duplicate Sheaf file, which this repair corrects.

Searches actually run with `msearch.py`: LeanFinder on etale qcqs finite constructible
stratification returned only general etale/quasi-finite declarations; Loogle on the exact
theorem name returned unknown identifier; grep on the theorem/module names returned no
indexed hits. Direct `rg` over the local adopted-source and Sheaf trees found the exact
upstream implementation, then a byte comparison from the module header confirmed identity.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
