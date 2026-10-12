## What changed

Proved `Ideal.isNoetherianRing_fiber` in
`Sheaf.RingTheory.FibreRingNoetherian`, with its signature unchanged.
Added proof-only imports `Mathlib.RingTheory.Ideal.Quotient.Noetherian` and
`Mathlib.RingTheory.Localization.Submodule`. Both are necessary: removing the former
loses the Noetherian quotient instance; removing the latter loses the Noetherian
localization instance (both checked by compilation).

The proof follows the existing three-step DAG argument. Give the fibre its right-factor
B-algebra structure, let S be the localization of B at the image of the prime complement,
and obtain Noetherianity of S by its Mathlib instance. The quotient is Noetherian by
`Ideal.Quotient.isNoetherianRing`; transport this instance through the inverse of
`Ideal.Fiber.algEquivQuotient` using `isNoetherianRing_of_ringEquiv`.
The quotient and equivalence permanence results implement the final surjective-image
step. The node's existing proof, dependencies, and origin still describe this argument,
so no node change is needed. No unit statement or realized step is bypassed.

## Proved and sorry left

Proved `Ideal.isNoetherianRing_fiber`
(node `lem-weil-pbc-fibre-ring-noetherian`): 1 of 1 original sorries closed.
No sorry remains in the item, and none is added elsewhere. No new declarations or nodes.
Local compilation is clean. The delivery dry run checks the axioms and server compilation.

## No longer needed

None. No original imports were removed. The proof retains all ingredients of the
existing DAG route: localization at a prime, the definition of Noetherianity, the
fibre/localization-quotient isomorphism, localization permanence, and surjective-image
permanence (through quotient and equivalence transport). No nodes or modules are pruned.
The briefly tested omission of either added proof import failed, so both are retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The planned ingredients are already proved in Mathlib,
so no intermediate Sheaf statements need importing or splitting. This works without
Noetherianity of A, finite type of B over A, or nontriviality of B; the zero-ring case
is covered by the localization, quotient, and equivalence instances as stated.

## Second reading by T2

1. Passed: diffed the only delivered module against the read-only repository. The
   existing declaration signature and all definitions/docstrings are byte-for-byte
   unchanged. Only the proof and two plain proof-only imports differ; no change
   record is required.
2. Passed: local compilation is clean. A scratch copy with
   `#print axioms Ideal.isNoetherianRing_fiber` reports exactly `propext`,
   `Classical.choice`, and `Quot.sound`. There are no remaining sorries, hollow
   definitions, or forbidden declarations/attributes in the delivered file.
3. Passed: no statements or nodes are split off or added. Checked the localization
   and quotient argument also for zero B and for primes whose complement maps to
   zero in B: the localization and fibre may be zero, and the same Noetherian
   instances and equivalence apply without nontriviality assumptions.
4. Passed: read the Mathlib equivalence and permanence implementations and searched
   Mathlib again for Noetherian fibre/residue-field results using different words.
   No direct replacement was found. The four-line proof already takes the short
   Mathlib route. Both added imports supply necessary permanence instances.
   The original imports expose the notions in the signature. No old proof
   dependency is bypassed, so `No longer needed: None` is complete. Checked the
   unit records: no realized unit statement or step is removed or bypassed.
5. Passed: read the item node and all five proof dependencies. Localization
   Noetherianity, the fibre/localization-quotient equivalence, and quotient plus
   equivalence transport implement the node's three steps; its definition
   dependencies and source-based proof origin remain applicable. No node update
   is needed.

Second reading changed only this report by adding the review; the Lean proof was
retained unchanged.
