## What changed

Proved `exact_free_complex_last_minors_regular_sequence` in
`Sheaf.AlgebraicGeometry.ExactFreeComplexLastMinors`, with its signature and public imports
unchanged. The proof implements induction on the complex length, quotient reduction via the
existing `free_complex_mod_nonzerodivisor_exact`, entrywise preservation of the complex relation,
base change of maximal-minor ideals, exclusion of the unit-ideal quotient case, lifting a list
inside the ideal, and prepending the nonzerodivisor using Mathlib's regular-sequence criterion.
All auxiliary list, determinant, and regular-sequence glue is proved in private theorems.

Added the proved module `Sheaf.RingTheory.NonzerodivisorInInjectiveMaximalMinors`, containing
`Matrix.exists_nonZeroDivisor_mem_maximal_minors`. It packages the existing plan's associated-prime
and prime-avoidance steps. Its proof uses Mathlib's finiteness of associated primes, zero-divisor
union, prime avoidance, localization of associated primes, and the existing depth-zero unit-minor
lemma. A private proved helper identifies coordinatewise finite-product localization and proves
that the entrywise localized matrix remains injective by clearing an annihilating denominator.
No objects or definitions are chosen from unproved existence statements.

The item's direct import of `Sheaf.RingTheory.UnitMaximalMinorOfDepthZero` is replaced by the new
proved helper module. That dependency remains imported by the helper. Only proof imports were
added or moved. The original DAG node now follows the actual Lean induction; the new node records
the proved intermediate matrix statement. No existing statement, definition, or interface changed.

Validation: both delivered modules compile via the supplied launcher. The final delivery dry run
checks all declarations with the maintainer's axiom/sorry probe and checks the delivery records.

## Proved and sorry left

Closed the sole original hole:
`exact_free_complex_last_minors_regular_sequence`
(node `lem-weil-pbc-exact-free-complex-last-minors-regular-sequence`).

Also proved `Matrix.exists_nonZeroDivisor_mem_maximal_minors`
(node `lem-weil-pbc-injective-maximal-minors-nonzerodivisor`).
Every private helper in both modules is proved. No `sorry` remains in either delivered module,
and no new holes are added or split off. This is a proof from the existing planned dependencies,
which still contain their original holes:
`free_complex_mod_nonzerodivisor_exact`
(node `lem-weil-pbc-free-complex-mod-nonzerodivisor-exact`) and
`Matrix.exists_isUnit_maximal_minor_of_annihilator_eq_maximalIdeal`
(node `lem-weil-pbc-depth-zero-injective-free-map-unit-minor`). Their proofs are next-stage items;
this delivery does not modify them. The item is not claimed to have a sorry-free transitive closure.

## No longer needed

No original mathematical dependency or module is pruned from the combined proof. The direct
unit-minor import is moved into the new proved helper, not eliminated from the import closure.
The associated-prime/localization/prime-avoidance nodes previously listed on the item are now
listed on the helper node; they remain needed. No blueprint unit statement or proof step is bypassed.
Removed the redundant proof import
`Mathlib.Algebra.Module.LocalizedModule.IsLocalization` from the new helper: it is already
publicly imported through both associated-prime localization and finite-product base change.

For completeness, the old direct proof dependencies moved to the helper node are:
`def-weil-pbc-localization-at-prime`, `def-weil-pbc-module-localization`,
`lem-weil-pbc-localization-noetherian`,
`lem-weil-pbc-associated-prime-localization-depth-zero`,
`lem-weil-pbc-localization-module-exact`,
`lem-weil-pbc-depth-zero-injective-free-map-unit-minor`,
`lem-weil-pbc-noetherian-associated-primes-finite`,
`lem-weil-pbc-noetherian-zerodivisors-union-associated-primes`, and
`lem-weil-pbc-prime-avoidance`. None is pruned from the transitive proof.

## Where the brief, the DAG or earlier work was wrong

No mathematical error or statement correction was necessary. The proof uses exactly the original
induction route. The rank-zero case needs no special branch: the empty determinant generates the
unit ideal, and the proof's unit-ideal branch handles it. The new matrix lemma also works without
locality; locality is needed only by the main theorem's proper-ideal quotient induction.

The local literature checkout does not include `literature/stacks-project/algebra.tex`; the
specified source was read at https://stacks.math.columbia.edu/tag/00N1. LeanSearch returned an
internal service error, which is recorded as unavailable rather than as evidence of no match.
Loogle, LeanFinder, and local source searches were used independently.

Edge cases checked for the new statement: zero columns give the empty minor one; the zero ring
also has one as a nonzerodivisor in the injectivity sense; in positive column rank an injective
matrix cannot violate the conclusion even if there are fewer rows, because the localization
unit-minor lemma excludes that configuration. For the main proof, length one uses the empty
regular list over the nonzero quotient, and length at least two uses precisely the range of
indices in the reduction theorem.

## New nodes

`lem-weil-pbc-injective-maximal-minors-nonzerodivisor`, at
`dag/nodes/sec-proper-base-change/lem-weil-pbc-injective-maximal-minors-nonzerodivisor.json`, records
the new proved matrix lemma in `Sheaf.RingTheory.NonzerodivisorInInjectiveMaximalMinors`.
It is strictly the nonzerodivisor-selection part of the original argument: it has no complex,
no length parameter, and no regular-sequence conclusion. Its docstring gives the full argument
and source; its proof steps name the existing localization and associated-prime dependencies.
No change record is necessary because no existing interface is changed. No forced adaptations.

## Second reading by S3

1. **Interface preservation: PASS.** Compared the complete original module with the sandbox
   using `diff`. Independently compared the original theorem signature as text: byte-for-byte
   identical. All original public imports and the existing docstring are unchanged. The only
   existing node fields changed are `proof`, `proof_deps`, and `proof_origin`. No statement or
   definition change, change record, or forced adaptation is present.
2. **Proof and axioms: PASS.** Both modules compile cleanly through `lcompile.py --all`.
   Searched the delivered Lean for sorry, axiom, unsafe, opaque, implemented_by, extern, and
   kernel-check bypasses: none. Scratch copies with `#print axioms` checked all four private
   helpers and both public theorems. Private helpers use only propext, Classical.choice, and
   Quot.sound (the list-lifting helper needs only propext and Quot.sound). Both public theorems
   also report sorryAx solely through the two existing imported open theorems named above.
   No data construction selects a witness from an unproved mere-existence theorem.
3. **New and split-off statements: PASS.** No new hole or split-off open statement. The new
   proved helper is strictly the matrix-selection part of the argument, with no complex or
   regular-list conclusion. Checked zero columns, zero rows, the zero ring, square rank one,
   and the impossibility of positive injective column rank with fewer rows over a nonzero
   Noetherian ring. Its docstring and node explain localization and prime avoidance. Repeated
   searches independently with Loogle, LeanFinder, msearch grep, and direct rg over Mathlib,
   upstream modules, and Sheaf. Found square-matrix implications and existing weaker minor
   lemmas, but no existing theorem giving this rectangular minor-ideal conclusion. Added the
   independent Loogle search to its node.
4. **Route and pruning: PASS after import cleanup.** Checked the induction at e=1, the shifted
   indices for e>=2, the proper quotient ideal, determinant base change, and regular-sequence
   lifting. Read [Stacks Tag 00N1](https://stacks.math.columbia.edu/tag/00N1), especially its
   associated-prime and quotient-induction argument. The library's planned two open lemmas
   are used; no simpler matching theorem was found. Read the unit `sk-thm-p1` including all
   `realized` fields: this algebra lemma is below its realized statement and steps, and the
   chapter/unit route is preserved. No original dependency is pruned transitively; the nine
   dependencies moved to the helper are explicitly listed under No longer needed. Removed
   one redundant proof import from the new module; public imports serve signature notions.
5. **DAG agreement: PASS.** Read both delivered nodes and checked that proof steps correspond
   to the Lean, proof_deps equal the union of step uses, and all referenced node IDs exist.
   The original node records quotient induction and the proved helper. The helper records
   associated-prime finiteness, prime avoidance, localization, and the depth-zero minor lemma;
   its new-node metadata, verbatim Lean statement, source, and searches are supplied.

Second reading changed only the redundant IsLocalization proof import, the helper node's
independent search evidence, and this report's dependency accounting and review. No mathematical
proof repair was required. Closed one original hole; added zero holes; split off zero holes.
