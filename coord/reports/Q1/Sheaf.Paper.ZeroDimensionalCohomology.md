## What changed

Repaired both points of return X-f431e (head f431e23f6).

A: Moved the complete docstring and declaration of
`AlgebraicGeometry.zero_dimensional_etale_cohomology_rest` unchanged into its own
module, `Sheaf.Paper.ZeroDimensionalEtaleCohomologyRest`, at
`lean/Sheaf/Paper/ZeroDimensionalEtaleCohomologyRest.lean`. The new module has the
four original public imports, source/blueprint module docstring, exposed public
section, universe, opens and namespace. The item imports it privately. Updated
`zero-dimensional-etale-cohomology-rest.json` to record its new module and file.

B8: Replaced the base-change-points proof-only import with
`Mathlib.AlgebraicGeometry.Artinian`. The finiteness proof now installs local
Noetherianness using `LocallyOfFiniteType.isLocallyNoetherian f`, compactness using
`QuasiCompact.compactSpace_of_compactSpace f`, and local Artinianness using
`IsLocallyArtinian.of_topologicalKrullDim_le_zero hdim`. Discreteness follows by
instance inference, and `finite_of_compact_of_discrete` gives `Finite C`.
Updated both affected docstrings and the finite-helper node's proof, dependency
and proof-origin records; updated the item's first proof step accordingly.
All existing theorem signatures and the remainder's proof plan are unchanged.

## Proved and sorry left

`AlgebraicGeometry.zero_dimensional_etale_cohomology` is proved by pairing the
finiteness theorem with the two cohomological conclusions of the remainder.
This closes the original module's one sorry by a reduction with a separately
proved geometric conjunct.

`AlgebraicGeometry.zero_dimensional_etale_finite`, node
`zero-dimensional-etale-finite`, is proved directly from Mathlib, without an
imported sorry dependency.

The delivery's sole remaining sorry is
`AlgebraicGeometry.zero_dimensional_etale_cohomology_rest`, node
`zero-dimensional-etale-cohomology-rest`, in the new module
`Sheaf.Paper.ZeroDimensionalEtaleCohomologyRest`. It states positive-degree
vanishing and invertibility of the exact canonical degree-zero stalk map.
The unchanged source/docstring proof describes finite reduction, coproduct
cohomology, universal-homeomorphism transport and canonical germ compatibility.

## No longer needed

Removed the import `Sheaf.AlgebraicGeometry.ZeroDimensionalBaseChangePoints` and
its finiteness proof dependency `lem-weil-pbc-zero-dimensional-base-change-points`.
The theorem `AlgebraicGeometry.zeroDimensional_baseChange_points` and its other
base-change conclusions are unnecessary for this item's proof. The finite
helper instead cites the Mathlib leaf
`lem-weil-pbc-finite-type-dim-zero-artinian`.

No further imports were removed. The remainder retains its eight documented
geometric/cohomological proof dependencies; their transitively needed nodes are
not pruned by this repair. The unit's finite-point acyclicity route is preserved.

## Where the brief, the DAG or earlier work was wrong

A: The previous delivery left the new remaining-sorry theorem in the item's
module, preventing it from becoming a separate worker item. It now has its own
module and matching node record; its text was moved unchanged.

B8: The previous finite helper needlessly depended on the unproved
base-change-points theorem. The existing Artinian Mathlib leaf already records
all facts needed for finiteness, so the repaired proof uses those directly.
The report's previous projection-based description and stale second-reading
claims have been removed. A second reader supplies the new reading separately.

## New nodes

`zero-dimensional-etale-finite` remains the delivery's node for the proved
finiteness conjunct, in `Sheaf.Paper.ZeroDimensionalCohomology`; its only proof
dependency is now `lem-weil-pbc-finite-type-dim-zero-artinian`.

`zero-dimensional-etale-cohomology-rest` remains the delivery's node for the
strict cohomological remainder, now in
`Sheaf.Paper.ZeroDimensionalEtaleCohomologyRest`. Its signature, source and proof
steps are unchanged. No additional node or statement-change record was needed.

## Second reading by Q1

1. **Visible changes and statements.** Compared the delivered item with the repository version. Existing theorem signatures are unchanged; the added finite helper and moved remainder have the exact declarations recorded by their nodes. The only changes to existing declarations are proof/docstring/import changes declared in this report.
2. **Proof checks.** Compiled both sandbox modules with `lcompile.py --all`. There is one intentional `sorry`, only in `zero_dimensional_etale_cohomology_rest`, with its split node and source documentation. The finite helper and main theorem have no local `sorry`; the finite helper's axioms are only `propext`, `Classical.choice`, and `Quot.sound`, while the main theorem inherits the intentional remainder `sorryAx`.
3. **Split statements.** Checked the remainder statement against the original target conjunct and its node; it is the strict cohomological remainder, not a restatement of the full item. The finite helper is a genuine geometric finiteness reduction and is proved directly from Mathlib. No duplicate declaration was found in the repository or Mathlib search record.
4. **Pruning and route.** The proof uses the shorter Mathlib Artinian/compact-discrete route for finiteness and retains the unit's cohomological remainder route. Removed the old base-change-points import and dependency as documented; no other proof dependency is unused. Proof-only imports are private.
5. **DAG agreement.** Checked the item and both split/proved node records: module, declaration, proof steps, dependencies, and proof origins match the Lean files. The unit route remains represented by the remainder node.

Changed after reading: no mathematical or statement repair was needed. Verified the sandbox delivery and retained the documented split and pruning decisions.
