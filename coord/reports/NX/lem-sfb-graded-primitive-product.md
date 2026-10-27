# Stage-1 report: lem-sfb-graded-primitive-product

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-graded-primitive-product.json: item, split; statement unchanged; four explicit induction steps, 1880 proof-text characters in total, longest step 567 characters.
- dag/nodes/sec-six-functors-basics/lem-sfb-linear-map-extension-prescribed-value.json: statement; Mathlib leaf, LinearMap.exists_extend_of_notMem, Mathlib/LinearAlgebra/Basis/VectorSpace.lean:294–301.
- citations.json: one verbatim statement quotation for each of the two step citations.
- searches.jsonl: actual msearch.py results, retained as returned.

## Attachments

None. Project searches for the item tag, primitive homogeneous elements and primitive products found no matching project declaration. Existing group-cohomological cup nonvanishing has different objects and hypotheses. Mathlib search hits for group-like elements are not primitive-element statements.

## WANTED

None. The required Milne reference, Stacks tensor construction and Mathlib sources are locally readable.

## Findings and changes

The item had no proof and the sandbox had no earlier node or report. I preserved its full statement, including noncommutative associative multiplication, all characteristics and the empty family. The source is Milne, Abelian Varieties, I Lemma 12.2, printed p.55. I read its proof: it invokes Borel's structure theorem for a bounded anticommutative algebra over a perfect field. This item deliberately isolates a more general primitive-product ingredient, so my proof is marked agent-written; it does not pretend Milne states the current item verbatim or establishes the full structure theorem by this argument.

The proof uses binary coproduct expansion and induction on the number of factors. A functional annihilating degrees other than one and the preceding degree-one vectors detects the prefix product in the coproduct of the full product. The general extension theorem is the only new node; it is a genuine general linear-algebra theorem, not a clause of the item or a renamed primitive-product statement. No graded bialgebra expansion lemma, tensor-coordinate detection lemma or separate characteristic-two lemma is created: the subset expansion and its sign recurrence are written in the item itself.

I read the chapter and DAG unit and the corresponding current latest-blueprint unit and direct-image proof. The DAG unit record has an older chapter assignment, whereas latest places this unit in six-functors-basics. The item's inherited chapter/unit and its null blueprint ancestor are retained. The ancestor command returned None; whole-blueprint searches for primitive, linear functional, linear map and extend and latest-source searches found no equivalent node. This supporting algebra lemma stays below the inherited coherent H1 dimension argument in the alteration route; it does not change the chapter or unit route. No unit realization fields are applicable.

## Not duplicates

lem-sfb-linear-map-extension-prescribed-value vs lem-sfb-proper-subspace-separating-functional: the existing statement assumes a finite-dimensional vector space and supplies a nonzero annihilator of a proper subspace; the new statement extends arbitrary vector-valued linear maps on arbitrary-dimensional spaces and prescribes a value at a specified outside vector. The item needs a functional on the possibly infinite-dimensional H and normalization at x_r, neither supplied by the existing node's statement.
lem-sfb-linear-map-extension-prescribed-value vs lem-weil-pbc-finite-kernel-scalar-extension: the existing statement concerns finite-dimensional scalar-extension kernels and only approximation up to a finite-rank error; it supplies no exact extension with prescribed value. Its proof's use of LinearMap.exists_extend cannot be borrowed as a statement.
lem-sfb-linear-map-extension-prescribed-value vs lem-sfb-bounded-extension-zorn: that statement is a conditional extension of a functional preserving a nonarchimedean bound, with one-vector extendability as a hypothesis. It is not the unconditional algebraic prescribed-value theorem.
lem-sfb-linear-map-extension-prescribed-value vs lem-sfb-ultrametric-one-vector-extension: that statement assumes a complete nonarchimedean valued field, a norm bound, finite-dimensional target and compact admissible scalar sets; it is not a theorem over arbitrary fields and vector spaces with arbitrary prescribed value.

No Stacks tag occurs in the new leaf's source. The reused tensor definition is exactly the ordinary module tensor product, not sheaf or derived tensor.

## Review by NX

I read Milne I Lemma 12.2 and its preceding Hopf-algebra discussion on printed p.55. I checked the leaf against Mathlib/LinearAlgebra/Basis/VectorSpace.lean:294–301, including the surrounding DivisionRing, AddCommGroup and Module hypotheses; a field satisfies the scalar hypothesis and neither source nor item assumes finite dimension. I also opened def-weil-field and def-weil-pbc-module-tensor-product. For the latter I read Stacks algebra.tex, lemma-tensor-product (Tag 00CX), and its definition after the lemma: its universal property gives a linear map for every bilinear map to any module. There is no source error or statement dispute to repair.

Step 1 uses no cited theorem: it states the induction claim uniformly, includes r=0 and extends a prefix relation by zero, so the inductive hypothesis is legitimate. Step 2 cites exactly the new leaf, whose statement promises g restricted to P equals f and g(v)=u; the citation quote contains both conclusions. Here P is explicitly a k-subspace of H, f=0 is linear, U=k, and degree-one projection together with independence proves x_r outside P. The chosen functional therefore annihilates every homogeneous component except degree one and has exactly the required values on all x_i. No basis extension or finite-dimensional separation result is silently used.

Step 3 uses only distributivity, the given multiplicativity/primitivity, and the signed multiplication in the hypothesis. I verified the sign recurrence: adding a new left tensor factor crosses each earlier right tensor factor, while adding a right factor crosses none. This is a single routine expansion of a finite product, with both the starting term and recurrence written out. It hides no independent comparison or standard lemma. Step 4 cites the tensor definition's actual universal property: (a,b) maps to lambda(b)a is bilinear, so T exists and is linear. The only surviving subset is {r}; its sign is +1 and its image is the nonzero induction prefix. Thus assuming the full product zero contradicts linearity of T and Delta. The quote is copied verbatim from the tensor node, not reconstructed from its proof. These two citations are all the non-elementary inputs; proof_deps is exactly their union.

For B1–B10 I checked that the only new node is statement-only and self-contained, its field has the correct definition dependency, its TeX has single mathematical backslashes, its source names the exact read declaration and lines, and its search records reproduce actual logged queries. It is a one-line specialization of the Mathlib theorem, not a candidate needing a comparison proof. I searched all DAG statements/titles, blueprint references and project Lean before creating it; the near matches above were opened and rejected by their actual statements. For C1–C8 each proof citation was checked against its statement, the elementary portions are explicitly written, no proof-only construction is borrowed, and the two proof dependencies are terminal Mathlib nodes, so they cannot create a cycle. The tensor definition is a general mathematical tool and already a Mathlib leaf; it substitutes no unit-level geometric route.

For D1–D5 the item's own induction and coproduct computation carry its argument; the new node mentions no grading, coproduct or product, and no whole clause is moved into it. There are no omitted-details citations. For E1–E7 I checked the small cases and hypotheses: r=0 gives the assumed nonzero unit; r=1 gives T(Delta(x_1))=1; r=2 expands to x_1x_2 tensor 1 + x_1 tensor x_2 - x_2 tensor x_1 + 1 tensor x_1x_2, whose image is x_1. In characteristic two the minus becomes plus but its term is killed, so the survivor coefficient remains 1. Degree-one squares may be nonzero (e.g. the one-generator free tensor algebra) and are never assumed zero. Noncommutativity causes no reordering of x_i inside either subproduct. Arbitrarily large H^1 is allowed. Coassociativity, connectedness and degree preservation are stronger than this calculation requires, but all original hypotheses are retained. Every proof step is under 2000 characters; there is no long step to hide a lemma. There are no SGA citations, no Lean writes and no compiler/build calls.

## Unfinished work

None in the split. The delivery still requires the maintainer's independent review after the required dry run and push.
