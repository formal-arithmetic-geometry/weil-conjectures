## What changed

Completed the restriction, same-cover scalar-model, rank-zero presentation, zero-extension,
identity-cover, adapted-stratification and constructibility arguments in
`AlgebraicGeometry.ProEtale.scalarModelRestrictionCriterion`.

Added proved private helpers: `zero_presentation`, the `LocalModel` structure,
`cons_family`, and `transfer_family`. The explicit dependent motives and private wrapper
avoid costly unfolding of concrete pullbacks during finite-index transport. Local
irreducibility attributes and the declaration-local transparency option affect elaboration
only; no imported public definition changes.

Repaired the interface by adding `hE_n : E.n = S.n + 1`, retaining both original
heterogeneous equalities of domain and immersion families. The two unused geometric
hypothesis binders are prefixed with underscores to satisfy the warning gate. The intended extended
stratification has the complementary stratum followed by the old strata. The change record
is `coord/changes/B9-scalar-model-restriction-index-count.md`; the node records both DAG
users. Neither current consumer applies the theorem, so no consumer adaptation is needed.
The item and the unchanged direct importer `Sheaf.Paper.OpenExtensionConstructibleFiniteTor`
both compile through `lcompile.py --all`.

## Proved and sorry left

The repaired `AlgebraicGeometry.ProEtale.scalarModelRestrictionCriterion` has a complete
proof. `#print axioms` reports exactly `propext`, `Classical.choice`, and `Quot.sound`.
Remaining holes: zero. Added holes: zero. Split off: zero. The old module had one
hole, but its statement has changed; this is an interface repair with a proof, not a claim
that the earlier under-specified Lean proposition was proved unchanged.

## No longer needed

Removed the private imports `Mathlib.CategoryTheory.Adjunction.CompositionIso` and
`WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`: the public statement imports
already expose the required composition, pullback and zero-object APIs. All five declared
proof dependencies remain used. No DAG node or module is withdrawn or pruned.

## Where the brief, the DAG or earlier work was wrong

The stage-2 encoding omitted the explicit count of the specified extended stratification.
The two heterogeneous equalities do not provide a usable equality of the index counts.
The added count equation states exactly what the intended construction supplies. The source
argument works with zero old strata, an empty complement, zero coefficients and nonreduced
schemes. Generic equality elimination and finite case analysis implement its last step.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
