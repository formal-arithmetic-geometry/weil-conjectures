## What changed

Proved `AdicCompletion.local_tensor_quotient_power_bound` directly from Mathlib.
Integral incomparability puts each prime over p among the minimal primes of pS;
localization identifies the radical of pS_q with the maximal ideal of S_q.
Noetherian finite generation gives the pointwise exponent, and boundedness of
its finite range gives a uniform positive exponent. All added imports are proof-only.
The existing declaration signature and public imports are unchanged.

## Proved and sorry left

Closed: `AdicCompletion.local_tensor_quotient_power_bound` (the one original hole).
Added: none. Remaining: none. This is a proof, not a decomposition: the first
worker's pointwise hole is now proved within the original theorem.
The provisional `AdicCompletion.local_tensor_quotient_power_bound_each` and
`exists_uniform_bound_of_finite` declarations, their modules, and their new nodes
have been removed from the delivery.

## No longer needed

No repository imports were removed. The provisional proof-only imports
`Sheaf.RingTheory.LocalTensorQuotientPowerBoundEach` and
`Sheaf.RingTheory.FiniteUniformBound` are removed, together with those undelivered
modules and nodes. Redundant proof imports for IntegralClosure.Algebra.Basic,
Noetherian.Basic, and Finiteness.Ideal are unnecessary through the retained imports.

Old proof-dependency nodes no longer used by this route:

- `lem-weil-pbc-artinian-local-unique-prime`
- `lem-weil-pbc-finite-dim-algebra-artinian`
- `lem-weil-pbc-finite-type-algebra-noetherian`
- `lem-weil-pbc-localization-base-change`
- `lem-weil-pbc-localization-prime-residue-field-iso`
- `lem-weil-pbc-zero-locus-eq-iff-radical-eq`

These are pruned from this node's plan, not a claim that their modules have become
unreachable throughout the library. The finite-spectrum node remains to record
the finite-fibre ingredient; Mathlib supplies that ingredient directly.

## Where the brief, the DAG or earlier work was wrong

The first worker left a pointwise hole despite Mathlib providing a direct
minimal-prime route, and re-proved a finite maximum lemma already covered by
finite-set boundedness. Its report also omitted old dependencies removed from
the target node's new route. The second reading repairs all three issues.

## Second reading by P4

1. Compared the delivered module with the repository version using diff.
   The complete existing signature, universe parameters, docstring, and public
   imports are byte-for-byte unchanged. Only proof-only imports and the proof
   body change. No interface change record is required.
2. Compiled the submitted three modules, then the repaired final module through
   lcompile.py. Removed the submitted letI style warning. The final module has
   no sorry, axiom, unsafe, opaque, implemented_by, extern, or definitions.
   The scratch-copy axiom probe for
   `AdicCompletion.local_tensor_quotient_power_bound` reports exactly
   `propext`, `Classical.choice`, and `Quot.sound`, with no sorryAx.
3. Read both proposed new statements and nodes, checked the empty finite set,
   singleton fibre, field base, and nonreduced finite algebra cases. S=R gives
   exponent one. Removed both proposed nodes: finite boundedness is in Mathlib,
   and the pointwise assertion is now proved directly. Searches through msearch
   (LeanFinder, Loogle, grep), the upstream library and lean/ found the shorter
   route; no new public statement or unproved witness construction remains.
4. The final proof follows the original local radical-power and uniformization
   argument, with Mathlib shortcuts below unit level. Read dag/units/sk-thm-p1.json:
   this helper realizes neither the unit statement nor any unit step, and none
   of the realized nodes or routes is bypassed. Imports are restricted to the
   statement's unchanged imports and five proof imports used by this proof.
   The pruning list above includes every removed old proof dependency.
5. Updated the existing node's proof, proof_deps and proof_origin to describe
   integral minimality, localized radicals, Noetherian finite generation and
   finite boundedness. Its statement and all other existing fields are unchanged.
   No new node survives, and the node's new Mathlib dependencies already exist.

Changes by the second reader: closed the pointwise hole, removed both provisional
modules/nodes, simplified uniformization, removed redundant imports, fixed the
style warning, and corrected the DAG and progress/pruning report.
