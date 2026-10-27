# Stage-1 report: lem-sfb-kostant-rosenlicht-affine-orbits

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-kostant-rosenlicht-affine-orbits.json: statement, split; five proof steps, no Mathlib match.
- citations.json: 17 verbatim statement quotations, one per step/node citation.
- report.md: this report.

There are no new nodes and no new Mathlib leaves. The sandbox also holds the exact search log, a local pdftotext extraction and the script used to write the JSON; these are working files, not proposed DAG additions.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag and for Kostant, Rosenlicht, and unipotent/orbit combinations. No project declaration states the item. Mathlib searches through the required wrapper returned abstract topological orbit and coset facts, and a finite-group invariant-ring theorem; none supplies algebraic unipotent orbit closedness. The existing four inherited searches are retained and the four new item searches are appended. Further searches for a possible finite-subrepresentation input are in searches.jsonl; they were superseded by finding the exact existing DAG node, so no new node was created for it.

## WANTED

None for this delivery. The local Milne 2017 book contains the item and every algebraic-group argument used. The existing orbit-geometry node references a 2022 text, but its orbit and invariant-boundary clauses also appear in the local 2017 text, Propositions 7.4 and 7.5, pp.139–140.

## Corrections and provenance

The statement is unchanged. Removed def-sc-group-scheme-subgroup from stmt_deps: there is no subgroup construction in the statement. Milne's phrase “replace X with the closure of O” must mean the reduced closure for the later inference that a function constant on a dense orbit is constant on X. The split makes this explicit rather than assuming that the given Y is reduced. This is an explanation of the source's reduction, not a statement dispute.

The item has inherited blueprint.from.node = null. The ancestor command likewise returns None. Retained that provenance and its via list, filled same_as = [] after whole-blueprint searches for Kostant, unipotent and representation, and explained the realized Kostant–Rosenlicht input in split_report.blueprint. No chapter or unit is changed. Read the chapter, the unit, the three SETUP levels and the stage-1 contract. The proof stays within the item's Milne route below the fixed unit.

## Not duplicates

No new nodes. In particular, reused lem-sfb-comodule-finite-subrepresentation instead of creating a rational-module local-finiteness node. Also reused lem-sfb-unipotent-rational-representation-fixed-vector and lem-sfb-smooth-group-orbit-geometry. The project has these inputs even though Mathlib's search services did not find corresponding theorems.

## Review by Q29

I read Milne iAG2017, Theorem 17.64, pp.373–374, in the local PDF extraction; its proof chooses a nonzero invariant function in the ideal of the boundary and concludes that this function is a nonzero scalar. I also read Remark 4.1, Proposition 4.7 and Corollary 4.8, the coordinate-action paragraph in 4(d), and Propositions 7.4–7.5. There are no new nodes whose sources need a separate review.

For step 1 I opened the full statements of the affine-source separatedness lemma, the smooth-group orbit-geometry lemma, and the reduced-induced-closed-subscheme lemma. The first applies to the affine scheme Y over k. The second requires smoothness, connectedness, finite type, an algebraically closed field and a separated finite-type target; all hold here, with separatedness furnished by the first citation. Its statement supplies the actual orbit image, local closedness, faithful flatness, and invariance of the closure and boundary. I use these invariant loci with their reduced structures, exactly as Milne 7.5 does. The reduced-closed-subscheme statement constructs those structures and writes their affine coordinates as quotients. The finite-type assertion for the quotient is elementary: use the images of a finite generating set. This step does not invoke an unstated orbit quotient theorem.

For step 2, the reduced-closed-subscheme statement supplies the radical ideal I and V(I)=Z. Since O contains y, Z is proper; I=0 would force Z=X. The empty-boundary case is disposed of before assuming it is nonempty.

For step 3 I opened the affine spectrum definition, tensor-pushout statement, representation/comodule dictionary, finite-subrepresentation statement, vector-space-basis theorem and tensor-product definition. The coordinate action is written with an inverse so it really is a left representation on functions. Action identities give the two displayed coaction identities. Invariance of the closed subscheme Z makes the quotient coaction vanish on I. I wrote the vector-space direct-sum argument that identifies its kernel with I tensor k[V]; it does not presume flatness over an arbitrary ring. The base is a field. The finite-subrepresentation statement explicitly allows infinite-dimensional modules and a singleton subset, so it gives a nonzero finite-dimensional W inside I, rather than just inside A.

For step 4 the dictionary explicitly identifies finite-dimensional comodules with group-scheme representations. A basis identifies W with k^d; h ensures d is positive. The fixed-vector node requires a faithful matrix representation of the smooth affine finite-type group, unipotent on k-points. I checked that the unipotence definition supplies the stronger geometric condition and a closed immersion, hence the required functorwise injectivity. Its conclusion is only invariance on k-points, which is all step 5 uses. I did not claim scheme-theoretic invariance from that conclusion.

For step 5 I read the Jacobson-density and residue-field statements: they apply to V, which is finite type over the algebraically closed field, so V(k) is dense. Continuity gives density of its orbit image in the orbit closure. The vanishing locus of f-f(y) is closed. The reduced-closed-subscheme statement gives the zero radical ideal for the whole reduced affine X, so vanishing on all points implies equality in A. This explicitly resolves the issue with nilpotents in the ambient Y. A nonzero scalar in I is a unit, so I=A and Z is empty. The final reduced closed structure is a clause of the cited reduced-subscheme statement, not a definition being used as an existence theorem.

I checked delivery-errors B–E against the actual statements. No new unsplit nodes, hidden restatement nodes, or new notions are introduced. Every proof step cites all its non-elementary inputs; citations.json quotes the statements verbatim. Generic off-unit tools are declared only in split_report.tool_uses. All five steps are shorter than 2000 characters. Edge cases checked: the trivial group has singleton closed orbits; Y empty has no y and the assertion is vacuous; a nonreduced Y is handled by the reduced closure; a zero boundary ideal cannot define a proper boundary; zero-dimensional W cannot occur because it contains h != 0; positive characteristic causes no division except by a nonzero field scalar. No SGA source, Lean edits, compiler, Lake, repository writes or git commands were used.

## Unfinished work

None in the one-level split. Its cited nodes remain the existing DAG obligations. Delivery dry run and push are performed after this report is written.
