## What changed

Replaced the hole in `FieldTheory.exists_pBasis_extension` without changing its signature.
Added two proof-only imports: `Sheaf.FieldTheory.PBasisMaximalSuperset` and
`Sheaf.FieldTheory.PIndependentInsert`, together with Mathlib's basis construction module. All edits are in the assigned sandbox.

The extension proof establishes injectivity of the original family by comparing the
single-generator monomials, transports independence to its image, chooses a maximal
independent superset, derives spanning by contradiction using insertion, and constructs
and reindexes the monomial basis. The complement index type is a subtype of K, so it has
exactly universe v as required. The original index type can have any universe w.

`FieldTheory.exists_maximal_pIndependent_superset` is fully proved. Its private
`supportedExponentEquiv` and `pIndependent_iff_supported` identify bounded monomials
on a subset with ambient bounded exponent functions supported there. For a chain union,
finite supports lie in a single chain member; Mathlib's directed-union independence
lemma gives independence of the union. Zorn gives a maximal superset. No witness of an
unproved existence theorem is used to define data.

The remaining insertion statement isolates steps 3--5 of the old plan. Its conclusion
is just independence after adjoining ONE element outside the monomial span; it has no
maximality, extension witnesses, basis, or spanning conclusion. The maximality
contradiction and basis reindexing are proved in the original module.

## Proved and sorry left

Closed the original hole: `FieldTheory.exists_pBasis_extension`
(node `lem-weil-pbc-p-independent-extends-to-p-basis`). Its proof now rests on the
following single new hole, so this is a decomposition, not a sorry-free proof of the
overall mathematical theorem.

Also proved: `FieldTheory.exists_maximal_pIndependent_superset`
(node `lem-weil-pbc-p-independent-maximal-superset`). Its helpers and all helpers in
`PBasisExtension` are fully proved.

Added one hole, and this is every sorry in the delivery:
`FieldTheory.pIndependent_insert_of_not_mem_span`
(node `lem-weil-pbc-p-independent-insert-outside-span`, module
`Sheaf.FieldTheory.PIndependentInsert`). Its proof is exactly `:= by sorry`, with the
complete span-subfield, degree-p, and grouping argument in the declaration docstring
and its node. One upper hole closed, one lower hole added: net holes zero.

The three delivered modules compile cleanly with `lcompile.py --all`.

## No longer needed

None. No original import was removed. The original direct DAG dependencies
`lem-weil-pbc-zorn-lemma`, `def-weil-algebraic-element`, and
`lem-weil-pbc-simple-algebraic-extension-power-basis` remain needed transitively:
Zorn is used in the fully proved maximal-superset module; algebraicity and the
simple-extension power basis are used by the remaining insertion node's proof plan.
They are moved to the appropriate new nodes, not pruned. No unit statement or unit
proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original node calls chain-union independence and the monomial-span subfield
construction elementary. Chain-union independence required a support-preserving
Finsupp equivalence and directed-union independence argument, now fully formalized.
The span-subfield/degree-p/monomial-grouping portion remains explicit in the insertion
node; none of the old dependency declarations alone states it.

The source checkout paths in earlier project documents differ from this worker's
brief; the worker used the brief's Mathlib path. The local literature checkout does
not contain `literature/stacks-project/more-algebra.tex`; the source was read at the
official Stacks page https://stacks.math.columbia.edu/tag/07P2. Its X^p-x misprint is
already identified in the original node and is corrected to X^p-x^p in the new proof.
LeanSearch returned Internal Server Error. Searches record it as unavailable, not
as evidence of absence; LeanFinder, Loogle, msearch grep, and targeted local rg were
used instead. Blueprint searches for p-independent and 07P2 found no matching
blueprint theorem, and the existing DAG's 07P2 nodes were inspected for duplicates.

Edge cases checked mathematically: empty initial family and empty subsets; the empty
chain uses S as its upper bound. The zero monomial has empty support, so the nonempty
chain case also covers it. For p=2, the exponent 1 is still bounded and the difference
of single-generator monomials still detects injectivity. If k=K, or more generally
F=K, the span already contains 1 and is all K, so the insertion hypothesis cannot hold;
the conclusion is vacuous. If T is empty in a nonperfect extension, insertion reduces
to independence of 1,x,...,x^(p-1), exactly the degree-p argument. No extra finiteness
or nonemptiness hypotheses have been introduced.

## New nodes

`lem-weil-pbc-p-independent-maximal-superset`:
`Sheaf.FieldTheory.PBasisMaximalSuperset`, fully proved maximal-superset step of
Stacks 07P2. It has the same characteristic and coefficient-field hypotheses and
uses the existing Zorn node. The proof is independent of the extension theorem.

`lem-weil-pbc-p-independent-insert-outside-span`:
`Sheaf.FieldTheory.PIndependentInsert`, the one-element augmentation argument of
Stacks 07P2. It retains the original span-subfield and simple-extension proof route.
This is the only new unfinished statement and is strictly part of the original
extension argument. There are no change records or forced adaptations.


## Second reading by M3

1. Compared the delivered PBasisExtension module with the repository using diff and
   compared the literal text of the existing theorem signature through `:=`.
   Verdict: byte-for-byte unchanged. The existing docstring and all public imports
   are unchanged; the added imports are proof-only. No existing definitions changed,
   and there are no change records or forced adaptations.
2. Compiled all three modules locally with lcompile.py after the repairs. Verdict:
   clean. Read every proof and both private equivalence constructions: no hollow
   data, arbitrary witness from an unfinished existence theorem, axiom, unsafe,
   opaque, extern, or implemented_by. The only sorry is the entire public insertion
   theorem proof. Scratch-copy `#print axioms` checks give only propext,
   Classical.choice, and Quot.sound for the maximal-superset theorem; the insertion
   and extension theorems additionally use sorryAx, exactly as reported. The delivery
   tool also probes every declaration, including the private helpers.
3. Read the insertion statement, docstring, and node against Stacks Tag 07P2,
   especially its last two extension paragraphs. Verdict: true and strictly simpler
   than the original item, with no extension, maximality, or spanning conclusion.
   Checked T empty (powers 1 through x^(p-1)), p=2, and coefficient field equal to K
   (outside-span hypothesis impossible). The proof works for infinite T because each
   relation and exponent support is finite. The maximal-superset statement is fully
   proved, including the empty-chain case. Independent LeanFinder search used
   “restricted monomials” and “adjoining x outside the field”; Loogle searched
   linear independence of powers; msearch grep and local rg searched minpoly,
   monomial spans, and the field-theory directories. No existing insertion or
   maximal p-monomial theorem was found in Mathlib or either library root.
4. Followed the extension proof from injectivity to image transport, maximality,
   insertion contradiction, basis construction, and reindexing. Verdict: a real
   reduction, not a restatement. Mathlib's
   Polynomial.X_pow_sub_C_irreducible_of_prime offers a shorter future replacement
   for the insertion docstring's coefficient argument: a p-th root of x^p in L
   would equal x by injectivity of Frobenius. It does not supply the span-subfield
   or monomial-grouping construction, so the remaining hole cannot be closed by
   a direct application. Checked dag/units/sk-thm-p1.json realized: this item is
   below the unit level, and no realized statement or step is bypassed. The three
   old direct proof dependencies are all explicitly accounted for under No longer
   needed and remain transitive dependencies; no old dependency module is pruned.
   Removed the redundant proof-only Mathlib.Data.Finsupp.Basic imports in
   PBasisExtension and PBasisMaximalSuperset; the set still compiles cleanly.
5. Compared the existing node with the repository: only proof, proof_deps, and
   proof_origin changed. Checked the new nodes' statements against their Lean
   declarations, the union of step uses against proof_deps, source/proof_origin,
   creation metadata, searches, blueprint ancestry, chapter, and unit. Verdict:
   records match the Lean reduction; the Zorn dependency is the existing Mathlib
   zorn_subset leaf, and insertion retains the algebraicity and power-basis route.

Changes by the second reader: removed two redundant Mathlib.Data.Finsupp.Basic
proof imports, corrected the import description above, and added this review.
No mathematical statement or proof body changed. No further holes closed or added:
one original hole closed, one insertion hole added, net zero (a decomposition).
