## What changed

Completed the queued retirement of Sheaf.AlgebraicGeometry.Sites.FiniteGaloisInvariantGermDescent.
The module was already fully proved. Withdraw its local duplicate declaration and
point its node to the existing upstream module, whose text is unchanged. Adapt the
sole direct importer, Sheaf.AlgebraicGeometry.Sites.FieldInvariantGermRepresentative,
by integrating automorphism invariance and finite Galois descent into its proof.
The consumer's signature, public imports and smaller coefficient universe stay exact.
Update its node to cite automorphism extension and sections descent directly.

Repair of return at a5ea5fb3ad6: start from current sheaf-dag consumer, retaining
T2's upstream representative import, ULift import, and full ULift representative
construction (landed at 509f8f741dc). Reapply the direct descent argument after
that construction. The public signature and all public imports remain byte-identical.
The node copies preserve current metadata and record both parts of the proof.

Change record: coord/changes/U1-retire-finite-galois-invariant-germ-descent.md.

## Proved and sorry left

Zero original holes, zero holes closed, zero holes added, zero split off, zero holes
remaining in the delivered Lean files. This is retirement, not a new proof credit.
AlgebraicGeometry.Scheme.exists_fieldSection_of_invariant_germ remains completely proved.
The previously proved local exists_fieldSection_of_finiteGalois_invariant_representative
is withdrawn, not replaced by a sorry. The same-named upstream theorem is preserved.
The reconciled consumer compiled cleanly with lcompile.py on the project server
in 6.1 seconds, with no warnings or errors. No timeout or resource limit was raised,
and no file or proof was split. A separate server axiom probe (7.0 seconds)
reports exactly propext, Classical.choice and Quot.sound for the consumer theorem.
## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.Sites.FiniteGaloisInvariantGermDescent.
Removed its private import from Sheaf.AlgebraicGeometry.Sites.FieldInvariantGermRepresentative.
That consumer no longer uses lem-exc-field-invariant-germ-representative-identification;
its proof now uses lem-exc-galois-automorphism-extension and
lem-exc-finite-galois-sections-descent directly. Neither supporting node is pruned.
The retired node is retained with its upstream Lean attachment. No other module,
node, unit statement or unit proof step is withdrawn. All new imports support the
integrated proof: sections descent, automorphism extension, etale composition
continuity. The upstream finite Galois representative module supplies GaloisClosure. Retain
Mathlib.CategoryTheory.Limits.Preserves.Ulift for T2's coefficient-universe bridge.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an open sorry, but the actual queue marks this
zero-hole module as retire. Q1 already proved it on 2026-10-13. D5 generalized its
coefficient universe on 2026-10-20. The upstream counterpart still requires
Type (max (u + 1) v) and omits the unused hs premise; simply switching the consumer
import would fail at its existing Type (max u v). The direct integrated proof
preserves the generality of the consumer without changing an upstream interface
or creating another declaration of the same theorem.

Read Stacks etale-cohomology.tex, lemma-global-sections-point (Tag 04JM), the
existing dependency signatures and dag/units/sk-prop-h2.json. The unit route remains.
Fresh msearch.py searches: LeanFinder returned unrelated germ/spreading-out results;
Loogle found Point.toPresheafFiber_w_apply; grep returned zero hits. Direct rg found
the upstream theorem and its universe difference. No new mathematical statement
is introduced. The identity extension E=L, L=K and positive characteristic remain
covered by the same Galois tower and canonical-lift arguments.


The previous packet passed independent review but could not land because T2 had
changed the sole consumer after U1's base. This repair takes that current consumer
and integrates the direct descent proof without reverting T2's ULift bridge.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
