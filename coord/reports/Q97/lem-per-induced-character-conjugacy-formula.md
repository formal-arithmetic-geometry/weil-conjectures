# Stage-1 worker report: Q97

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-induced-character-conjugacy-formula.json`: item, now split into eight steps; no exact Mathlib match found.
- `citations.json`: eleven citations, one per occurrence in a proof step, with verbatim statement extracts.
- `searches.jsonl`: five searches run through the required msearch.py command. Their original outputs are also appended to the item's inherited Mathlib search records.
- `report.md`: this report.

No new DAG nodes and no new Mathlib leaves. All dependencies already exist. The initial sandbox had only dispatcher markers, so there was no earlier split or report to preserve.

## Attachments

None. Searched the read-only project under `lean/WeilConjectures/` for the exact blueprint tag and for induced-character terminology. There is no declaration of this quotient-induction character formula. The additive characters induced along field traces are a different notion.

## Literature wanted

WANTED: J.-P. Serre, *Linear Representations of Finite Groups*, Part I Chapter 7, induced representations and the induced character formula, for lem-per-induced-character-conjugacy-formula. This book is not available in the supplied literature. The proof is explicitly agent-written, not attributed to an unread textbook.

## Corrections and scope

The imported item was statement-only; its statement is correct. Added the existing trace definition reference and its statement dependency, without changing the mathematical assertion. The direct sum used in the proof is referenced there rather than added to the statement's dependencies.

Read the latest blueprint's chapter and perverse unit, and the statement and proof of lem-per-artin-gabber-affine-curve. This item is inherited auxiliary representation theory below Step 3, through the existing Brauer/induction chain, not an assertion explicitly present in the blueprint. Read ILO, Expose X, Proposition 1.2 context, printed p.138 (PDF page 144): the representation-lifting assertion before (5) motivates the ancestor chain but does not prove an induced character formula. Its provenance is retained as motivation only. No SGA source is used and no unit or chapter route is changed.

The existing lem-per-finite-group-induction-calculus was inspected. Its *proof* constructs coset coordinates, but its *statement* gives dimension, direct sums, transitivity, reciprocity and the tensor identity, not that particular coordinate isomorphism. Consequently this delivery does not cite it for the coordinates. The actual maps and inverse checks are written out in Steps 3 and 4 from the tensor, quotient and direct-sum definitions. There is no new node repeating that lemma, a clause of this item, or a short elementary calculation.

## Mathlib and duplicate searches

Ran leanfinder with two different descriptions, leansearch for the centralizer form, loogle with `FDRep.character, Representation.ind`, and grep with `ind.*char|char.*ind|character.*induc` in RepresentationTheory. Inspected the hits and read Character.lean, Induced.lean and FiniteIndex.lean. Character averages, character conjugation invariance, induction/coinduction comparison and group class equations are not the requested formula. In particular, Mathlib's induction uses a coinvariant convention with action by right inverse multiplication; identifying that with the present quotient convention would itself require an argument. None is an exact attachment or one-line specialization of the whole item.

Searched the whole DAG's statements for trace/matrix, coset-basis and centralizer-fibre results. Ran blueprint_refs.py ancestor on the item and whole-blueprint searches for induced character, coset, character, trace matrix and endomorphism trace. Reused the existing basis, trace, tensor, quotient and direct-sum nodes. No same-statement blueprint node was found.

## Not duplicates

No new nodes were created. The potentially tempting induction-calculus citation was excluded for the statement-versus-proof distinction above.

## Review by Q97

I checked delivery-errors B through E against the node files and sources, rather than treating their dependency lists as evidence. Every cited node's statement was opened. For the item, the source situation is as described above: the latest blueprint and ILO were read for the inherited location, and the elementary character computation is supplied and labelled as agent-written. There are no new nodes with sources to audit.

Step 1 uses the tensor node's assertion that pure tensors generate and the quotient node's surjectivity/kernel and coset description. Expanding in the specified group-algebra basis yields the generators used. The left action preserves exactly the written balancing relation, so no additional descent theorem is presumed.

Step 2 uses lem-weil-pbc-vector-space-free, whose statement really gives a basis over any field, with the field specialized to C. The finite-dimensional definition gives a finite spanning family; the union-of-supports argument proves that the chosen basis is finite. No finite-basis conclusion is incorrectly taken directly from the freeness lemma. Left-coset representatives exist because the group is finite; the representative and the residual H element are unique by cancellation.

Step 3 uses the concrete finite-support family definition of a direct sum, the tensor universal property, and quotient cosets. The displayed balancing check ensures that B kills the entire relation span, making its value constant on each quotient coset. Step 4 uses the same direct-sum definition for its spanning inclusions and coordinatewise test for a zero family. The two composites are checked on generators and the coordinate basis is proved independent. These short explicit calculations do not assume a separate coset-coordinate theorem.

Step 5 uses precisely the trace node's matrix diagonal formula, on the finite basis just constructed. The condition for a diagonal block is t=s, equivalently s inverse g s in H. Step 6 uses that same node's explicitly stated trace invariance under matrix conjugation. Conjugation is by the action of h on W, where h belongs to H, so this does not require a G-action on W. The bijection S times H to G gives the factor |H|; positivity and characteristic zero justify division in C.

Step 7 cites no external theorem: for each conjugate k the maps c to c x0 and x to x x0 inverse are written, their centralizer/fibre membership is checked, and their composites are the identity by cancellation. Thus the fibre size and finite regrouping are proved, rather than inferred from a definition of a centralizer. This is a routine explicit bijection, not an omitted orbit-stabilizer lemma. Step 8 again uses the trace definition for the zero and identity matrices. None of these steps is over 2000 characters; their lengths are 454, 525, 647, 483, 438, 613, 589 and 480 characters.

I checked H=G, H={1}, G={1}, W=0, and g=1; no semisimplicity, irreducibility, normality, nonzero dimension or faithful action is used. Independently enumerated S3 with the nonnormal subgroup generated by (12) and its sign character: the induced traces are 3 at the identity, -1 at each transposition, and 0 at each 3-cycle. The all-elements sums and centralizer-weighted sums agree for all six elements. In Step 7 the fibre is a left centralizer coset C_G(g)x0; this verifies the orientation required by x inverse g x.

All eleven quotes in citations.json were verified to be literal substrings of the cited statements. The proof dependencies are exactly the union of step citations. The statement has no missing hypothesis or false clause, so there is no STATEMENT-DISPUTED correction. No repository, launcher, Lean or compiler output was written. There is no unfinished mathematical part of this split; independent maintainer review remains the delivery workflow's next step.

## Validation

The first required server dry run passed preflight, check_dag and review_split. Final text inspection caught and repaired two TeX inequality escapes in Steps 5 and 8; these are notation repairs only. The final dry run is repeated on that corrected content before pushing.
