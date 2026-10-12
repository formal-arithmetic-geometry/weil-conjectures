## What changed

Proved `AlgebraicGeometry.Scheme.Hom.quasiFiniteAtPoint_isolated_in_fiber` in
`Sheaf.AlgebraicGeometry.QuasiFiniteAtPointIsolated`, with its signature unchanged.
Added a proof-only import of `Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite`.
The affine isolated-point hypothesis is transported to the set-theoretic ring fibre,
then Mathlib's ring characterization gives quasi-finiteness of the localization.
`IsAffineOpen.arrowStalkMapIso` and `RingHom.QuasiFinite.of_comp` give the stalk
predicate. Mathlib's scheme characterization proves the first conclusion;
`fiberHomeo.isOpenMap` proves the second. Updated the item's DAG proof and dependencies.
The original declaration docstring describes the geometric source proof; the DAG
now records the shorter implementation of its affine/stalk identifications.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.Scheme.Hom.quasiFiniteAtPoint_isolated_in_fiber`
(node `lem-weil-pbc-quasi-finite-at-point-isolated`).
No holes remain in the module; no holes or declarations were added elsewhere.
This is a proof, not a decomposition. The local compiler accepts it without warnings.
The delivery dry run checks the axioms and compiles on the project server.

## No longer needed

Removed the redundant proof import `Sheaf.RingTheory.QuasiFiniteAtPrime`: it is already
publicly imported by `Sheaf.AlgebraicGeometry.QuasiFiniteMorphism`, and its definition
is still used. The public imports were preserved because they support the statement.

The explicit geometric fibre-product route no longer needs these nodes:

- `lem-weil-pbc-residue-field-point-naturality`
- `lem-weil-pbc-open-fibre-product`
- `def-weil-open-immersion`
- `lem-weil-pbc-spec-residue-field-identification`
- `def-pc-fibre-product`
- `lem-weil-pbc-fibre-product-affine-spectra`

Their Mathlib modules need not be imported separately for this proof; no additional
Sheaf statement module is needed. The ring quasi-finiteness definition and the
fibre-ring prime correspondence remain used. No node realizing the unit's own
statement or proof steps is bypassed (`sk-thm-p1.realized` was checked).
This list describes dependencies of this item, not a claim that no other item uses them.

## Where the brief, the DAG or earlier work was wrong

The earlier Mathlib search correctly distinguished the Stacks affine predicate
from the stalk predicate, but the missing bridge can be proved directly using
`Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber`, the affine stalk-map isomorphism,
and cancellation of quasi-finiteness through a composite. There is no statement
correction or disputed statement. No new nodes are needed.

## Second reading by N3

1. Compared the only delivered Lean module with the repository using `diff` and
   checked its theorem signature byte for byte. The signature, definitions, public
   imports, and existing docstring are unchanged. Only the proof and one proof-only
   import change; no change record is required. Verdict: pass.
2. Independently compiled the module locally without errors or warnings. A scratch
   copy with `#print axioms` confirms that
   `AlgebraicGeometry.Scheme.Hom.quasiFiniteAtPoint_isolated_in_fiber` uses only
   `propext`, `Classical.choice`, and `Quot.sound`. No sorry or forbidden declaration
   occurs in the delivery, and there are no definitions added. Verdict: pass.
3. There are no split-off statements or new declarations to assess. Reviewed the
   affine finite-type witness, singleton transport, local-ring-map composition,
   and Mathlib characterization; the argument uses the original hypotheses.
   The supplied point ensures nonempty affine neighborhoods and a prime, so empty
   schemes and zero rings introduce no missing case. Verdict: pass.
4. Searched Mathlib with `msearch.py grep` for `QuasiFiniteAt.*of`,
   `quasiFiniteAt_iff`, and `arrowStalkMapIso`, and searched both library roots for
   the project's predicate and conclusion. Read Mathlib's ring and scheme
   characterizations and affine-to-stalk bridge. Found no direct theorem for the
   project's Stacks predicate that avoids this bridge. The sole new import is
   proof-only; preserved public imports support the signature. The six removed
   proof dependencies are all listed under No longer needed. Checked the complete
   `sk-thm-p1.realized` record: no removed dependency realizes a unit statement or
   step, and the unit route is retained. Verdict: pass.
5. Compared the node JSON against the repository: only `proof`, `proof_deps`, and
   `proof_origin` changed. The three steps describe the Lean argument, and the
   union of their uses equals `proof_deps`. There are no new nodes. Verdict: pass.

Second reading changed only this report by adding the independent review. No
repair of the proof or node was needed. One existing hole is closed and zero
holes are added; this is a proof, not a decomposition.
