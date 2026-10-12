## What changed

Replaced the proof of `AlgebraicGeometry.Scheme.finiteLocalModels_descentDatum_exists`
without changing its signature. Chose the given local representatives inside the
existence proof and constructed their coproduct morphism explicitly as `Limits.Sigma.map`.
The private proved helper `finite_sigmaMap` proves the component squares cartesian from
`IsOpenImmersion.isPullback`, `sigmaMk` and `sigmaι_eq_iff`, then proves finiteness by
locality on the target. Etaleness is proved by source locality. The final Lean proof
transports the representation along the unit of `Etale.overEquiv` and whiskers the
presheaf isomorphism. No data definition uses an unproved existence theorem.

Added the proof-only import `Sheaf.AlgebraicGeometry.EtaleCoproductRepresentation`.
Its one theorem handles only sheaf representation by the explicitly specified etale
coproduct, independently of finiteness and independently of a cover of T.
Both modules compile together with `lcompile.py --all` without warnings.
Updated the item's node proof to match the actual construction and reduction.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.finiteLocalModels_descentDatum_exists`, node
`lem-weil-pbc-finite-local-models-descent-datum-existence`.
The item now has no sorry. `finite_sigmaMap` is proved completely.

Added one hole in `AlgebraicGeometry.Scheme.etaleCoproduct_representation`, node
`lem-weil-pbc-etale-coproduct-representation`.
This is a decomposition (one hole closed, one added; net zero), not a complete
proof of the mathematical assembly theorem. The new statement specifies the exact
coproduct object and omits finiteness entirely; the original proof supplies the
finite/etale construction and the localized-site transport in real Lean.
Its docstring gives the sectionwise gluing proof and includes the empty index case.

## No longer needed

Removed the direct proof-only imports
`Sheaf.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleDisjointCover`, replacing them
with `Sheaf.AlgebraicGeometry.EtaleCoproductRepresentation`. The second reading
retained these two proof-dependency imports in the split gluing module, where
they supply the planned gluing argument. All four original
public imports support the statement and the proved coproduct construction. No node is fully pruned: the disjoint-sections
and representable-sheaf nodes from the old plan remain needed by the new gluing node,
although they are no longer direct proof dependencies of the item. No module is
claimed to leave the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The original plan's cited declarations provide the coproduct, locality, and section
product interfaces, but do not already state the natural presheaf identification
between the two products in step 4. That gluing step is now an explicit, separately
stated theorem. Finiteness cannot be inferred using the finite-index sigmaDesc
instance: the cover index can be infinite. The new Lean proof uses target locality
and proves the component pullbacks instead, with no uniform rank bound.

The local Stacks .tex files named in the existing nodes are absent on this machine.
Read the online statements and proofs of Tags 03RV and 02W5. LeanFinder found
scheme disjoint coproducts and the general colimit interfaces; Loogle's query
`AlgebraicGeometry.Scheme.sigma` returned unknown identifier; grep found sigmaDesc
and locality APIs. LeanSearch returned Internal Server Error, recorded as unavailable.
A whole-blueprint search for coproduct/disjoint representation found no matching node.
The original unit route is retained: this node is below the unit realization boundary,
and all four original construction steps still occur either in Lean or in the gluing node.

## New nodes

`lem-weil-pbc-etale-coproduct-representation`, in
`lean/Sheaf/AlgebraicGeometry/EtaleCoproductRepresentation.lean`, states the
representation on an explicitly given coproduct of etale representatives. It needs
no finiteness or cover of T. Empty indices, empty components, infinitely many
components and unbounded finite ranks remain allowed. This isolates sectionwise
sheaf gluing from the proved geometric finiteness and site-equivalence transport.
No change record: no existing statement, definition, or public import changed.

## Second reading by H3

1. The target module was diffed against the repository. The existing declaration
   `finiteLocalModels_descentDatum_exists` has the same signature byte for byte;
   only its proof and proof-only imports changed. Verdict: pass.
2. Both sandbox modules compile with `lcompile.py --all` without warnings. The
   target hole is closed, and the only remaining `sorry` is the named theorem
   `etaleCoproduct_representation`; it has a complete docstring proof and a
   matching split node. Scratch-copy `#print axioms` for both public theorems
   shows only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` from
   the documented open gluing statement. No definitions contain `sorry`, and
   the construction is explicit. Verdict: pass.
3. The split statement is strictly narrower than the target: it assembles chosen
   representations on a specified coproduct and does not assert finiteness or
   cover surjectivity. It allows empty and infinite index types and is true by
   disjoint-cover sheaf gluing. It is not a restatement of the target. Verdict:
   pass. Independent grep search for `disjoint.*represent|represent.*coproduct|
   sheaf.*sigma` found general coproduct sheaf-condition interfaces, not this
   representation assembly statement. The existing disjoint-product and
   representable-sheaf declarations supply ingredients, not the complete result.
4. The proof follows the unit route: choose local finite etale representatives,
   construct the coproduct morphism, prove etaleness and finiteness by locality,
   then transport the representation through `Etale.overEquiv`. The new theorem
   isolates only the unresolved gluing step. Verdict: pass.
5. The target node's `proof`, `proof_deps`, and `proof_origin` match the Lean
   proof, and the new node records its declaration, source, route, and split
   status. The unit realization was read and remains unchanged. The two old
   gluing dependencies are now dependencies of the split node rather than
   direct dependencies of the target. Verdict: pass.

Changed after reading: corrected the removed-import account and appended this
review record, including independent search and axiom results. Added the two
planned proof-dependency imports to the split gluing module so its imports
agree with its DAG route and the old gluing modules remain reachable. No
statements or definitions were changed.
