## What changed

Proved `AlgebraicGeometry.Scheme.etale_units_stalk_evaluation_surjective` by
specializing the already proved `etaleUnits_stalk_evaluation_overfield_bijective`
to `AlgebraicClosure K` and taking its surjectivity component. The existing
signature, definitions, docstring and public imports are unchanged. Added only a
plain proof import of `Sheaf.AlgebraicGeometry.EtaleUnitsStalkEvaluationOverfieldBijective`.
Updated the existing node's proof, proof_deps and proof_origin to this route.

## Proved and sorry left

Closed the sole original hole,
`AlgebraicGeometry.Scheme.etale_units_stalk_evaluation_surjective`.
Added zero holes; none remain in the delivered module. This is a proof, not a
decomposition. Removed the first worker's proposed holed theorem
`AlgebraicGeometry.Scheme.etale_units_stalk_realizes` and its undelivered node
`new-etale-units-stalk-realizes`. No data is chosen from an unproved existence theorem.

## No longer needed

Removed direct proof imports `WeilConjectures.CategoryTheory.Sites.Torsor` and
`WeilConjectures.Mathlib.RingTheory.Etale.Field`. The latter remains transitively
needed by the overfield theorem; no whole-library module pruning is claimed.
Every old direct proof dependency is replaced by
`lem-sc-etale-units-stalk-evaluation-overfield-bijective`:
`lem-weil-pbc-finite-separable-extension-etale`, `def-sc-gm-torsor`,
`def-sc-galois-units-cohomology`, `def-weil-pbc-geometric-stalks`.
The three definitions remain statement dependencies, and the finite separable
extension result remains used within the overfield theorem.

## Where the brief, the DAG or earlier work was wrong

The first worker missed the existing proved overfield bijectivity theorem and
introduced an unnecessary geometric realization hole. Its proposed signature
also replaced the local `Ω` abbreviation by `AlgebraicClosure K`; restored the
repository signature byte for byte. The proposed new node had an abbreviated
Lean statement and no Mathlib searches; it is removed rather than delivered.

## Second reading by H4

1. Compared the complete module with the repository using diff. PASS: the only
   final changes are plain proof imports and the proof body; every existing
   signature is byte for byte unchanged, and no definitions are changed.
2. Compiled the delivered file locally with lcompile.py. PASS: no errors or
   warnings and no sorry or forbidden declarations. A scratch copy prints axioms
   of both the target and the reused theorem: only propext, Classical.choice,
   Quot.sound. No sorryAx.
3. Read the proposed split-off statement and checked its finite separable field
   construction, including a=1 and imperfect base fields. It is mathematically
   true, but unnecessary: searching the library revealed the stronger proved
   overfield theorem. Removed the helper and node; no new statements remain.
4. PASS: the shortest route is specialization of a proved library theorem, whose
   surjectivity proof explicitly constructs K(a), its pointed spectrum and the
   unit section. Removed unused direct proof imports and listed all replaced
   proof dependencies above. Read dag/units/sk-thm-br.json: its realized entries
   are empty and its Brauer-injection/Tsen route is unaffected; no realized step
   is bypassed.
5. PASS: the existing node now names precisely the reused theorem in proof_deps,
   explains specialization and projection in proof, and records the same Stacks
   source in proof_origin. Lean metadata remains unchanged. No new nodes or
   change records are needed.

Changed in second reading: removed the unnecessary split-off theorem and node,
restored the exact original signature, reused the proved overfield theorem,
pruned two direct proof imports, and corrected the node and report.
