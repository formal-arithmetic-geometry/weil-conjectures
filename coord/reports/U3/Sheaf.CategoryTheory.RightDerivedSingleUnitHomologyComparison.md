## What changed

Proved `CategoryTheory.Functor.rightDerivedPlusSingleUnitHomology_comp_comparison` in
`Sheaf.CategoryTheory.RightDerivedSingleUnitHomologyComparison`, with the existing
signature, definitions, and imports unchanged. The proof follows the two steps of
`lem-sbc-right-derived-single-unit-homology-comparison`: first cancel the derived unit on
the chosen injective resolution by naturality; then transport homology to the complex
and identify the augmentation by the degree-zero cycles inclusion.

The proof uses the existing comparison definitions and homology naturality in
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle`, and
Mathlib's `InjectiveResolution.toRightDerivedZero_eq`, `ι'_f_zero`, single-complex
homology lemmas, and extension homology/cycles comparisons. No left exactness is used.

## Proved and sorry left

Closed the single original hole:
`CategoryTheory.Functor.rightDerivedPlusSingleUnitHomology_comp_comparison`
(node `lem-sbc-right-derived-single-unit-homology-comparison`).

No sorry remains in the item. No new holes, statements, definitions, modules, or nodes
were added. This is a complete proof, not a decomposition.

## No longer needed

None. Both original public imports are needed by the existing definitions and statements.
The proof follows the original DAG route, so neither planned proof dependency is pruned.
The unit `sk-prop-deg0` has no realized node in this item's proof to bypass.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. LeanFinder, Loogle, the provided grep search, and local
searches found the comparison definitions and classical augmentation lemmas, but no
existing theorem proving this compatibility. The proof needs explicit transports between
the bounded-below subcategories and their ambient categories; these transports were proved
in the theorem using faithful inclusions and the quotient isomorphism's naturality.

Validation: local single-file compilation; required delivery dry run includes local and
server compilation, the project's axiom probe, and preflight. No repository writes or
pushes were made by the worker; the dry-run tool prepares and checks the delivery.

## Second reading by U3

1. **Interfaces unchanged — pass.** Compared the complete delivered module with the
   repository using `diff -u`. Both existing definitions, all assumptions, the theorem
   signature, docstrings, and public imports are byte-for-byte unchanged. Only the
   theorem proof and two theorem-local elaboration options were added. No statement
   change or change record is needed.
2. **Kernel proof — pass.** Independently compiled the delivered file locally without
   errors or warnings (4.0 seconds). Compiled a scratch copy with `#print axioms` for
   both definitions and the theorem: each uses exactly `propext`, `Classical.choice`,
   and `Quot.sound`; none uses `sorryAx`. Read the entire proof, including faithful
   transport, unit cancellation, homology naturality, and cancellation against the
   monomorphism into degree-zero complex terms. No prohibited declarations, hidden
   holes, or modified definitions occur.
3. **Split statements — pass, none.** No new declarations or holes were introduced,
   so no split statement needs edge-case testing or a new node. The proof does not
   invoke left exactness: the zero functor and zero object present no exceptional
   case, since all cancellations are against categorical isomorphisms or the cycles
   inclusion, never against an augmentation assumed invertible.
4. **Route and pruning — pass.** Read PlusSingle and the classical augmentation
   definitions and lemmas in Mathlib's RightDerived module; independently searched
   the upstream and Sheaf derived-functor modules for single/unit/augmentation
   compatibility and used launcher Mathlib grep with different search terms. No
   existing theorem replacing this compatibility proof was found. The proof uses
   the existing naturality and resolution comparison lemmas directly. Both public
   imports supply notions used in the unchanged definitions and statement. Neither
   old proof dependency is obsolete: the second supplies the classical augmentation
   construction and resolution lemmas, without using its left-exactness conclusion.
   Read `dag/units/sk-prop-deg0.json`: its realized statement and step lists are empty;
   no unit realization is bypassed. Nothing is pruned.
5. **DAG agreement — pass.** Read the item's node and both dependency records. The
   existing two proof steps describe exactly the proof: cancel the derived unit,
   then identify the mapped augmentation via cycles and homology. Its `proof_deps`
   and source-based `proof_origin` still agree; no node edit is necessary.

Changes by the second reader: added this independent review and the recorded axiom
verification. No mathematical or Lean repair was necessary; retained the proof.
