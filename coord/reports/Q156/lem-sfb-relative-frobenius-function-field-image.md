# Stage-1 delivery: lem-sfb-relative-frobenius-function-field-image

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-relative-frobenius-function-field-image.json: statement, now split in four steps; Mathlib has abstract field Frobenius maps but no match for the geometric image identification. Statement and stmt_deps unchanged.
- citations.json: verbatim statement quotations for all eight step/node citations.
- searches.jsonl: actual Q156 msearch results, five searches including two semantic phrasings.
- report.md: this report and review.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searches of lean/WeilConjectures for the item id, relativeFrobenius, relative_frobenius, relative Frobenius, and function-field notions did not find a project declaration giving the statement. The existing upstream sorry declarations are not attachments.

## Literature wanted

None.

## Findings and corrections

The imported statement is correct, including n=0; no statement dispute or change. The live item had no proof and no repair note. The sandbox initially had only dispatcher markers, so there was no previous split to discard. All inherited searches and blueprint provenance were preserved, and actual Q156 searches were appended.

The supplied affine-image source route can be carried out more economically with the existing lem-sfb-automorphism-twist-curve-lift: the projection from the scalar twist is an isomorphism of schemes, with explicitly stated pullback composition. This is a node-level argument for the same image identification in Stacks 0CCY/0CCG, not a replacement of a unit step. No k-linearity of the projection or of its function-field isomorphism is assumed. In particular, this avoids importing geometric integrality or tensor-injectivity without a cited theorem. The comparison node is in this same unit and has no dependency on the item.

## Unfinished work

None in this one-level split. The reused automorphism-twist comparison is now an existing split and L-reviewed item; its statement, rather than any argument hidden in its proof, is the dependency used here.

## Not duplicates

No new nodes. Whole-DAG tag search for 0CCG/0CCY and concept searches located lem-sfb-automorphism-twist-curve-lift and lem-sfb-frobenius-twist-geometric-integrality-affine, both read before deciding to reuse the former. Blueprint searches for relative Frobenius, power subfield and automorphism twist found no same-statement blueprint node. The existing trace-formula relative-Frobenius nodes have finite-field/Weil data rather than this function-field image assertion.

## Review by Q156

I read varieties.tex Definition 03SM (definition-absolute-frobenius), Lemma 0CC7 (lemma-frobenius-endomorphism-identity), and Remark 0CCG (remark-n-fold-relative-frobenius), and curves.tex Lemma 0CCY (lemma-inseparable-deg-p-smooth), including its equality of the image field with kK^p. I also read fields.tex Lemma 09GR (lemma-algebraically-closed), especially condition (3). These confirm the direction of the scalar twist, the two projections of relative Frobenius and the power formula. The proof is marked agent-written because the generic-stalk assembly expands this calculation rather than quoting a source proof verbatim. The chapter and unit records and their three-level route were read; this node serves the inherited high-genus-cover auxiliary argument below the unit, with that route unchanged.

Step 1 cites def-weil-ring-frobenius for the unital iterated homomorphism and def-weil-algebraic-closure for roots of nonconstant polynomials. I opened both statements: the former explicitly gives x mapped to x^(p^n), including n=0, and the latter explicitly gives a root of every nonconstant polynomial. Since p is the positive characteristic of a field it is prime, q=p^n is positive, and Z^q-b is nonconstant. Injectivity follows from (c-d)^q=0 in a field. Thus this short deduction does not hide a new perfect-field lemma.

Step 2 cites the absolute Frobenius definition for its identity topological map, the ring Frobenius definition for naturality, and lem-sfb-automorphism-twist-curve-lift. I read that comparison's whole statement: it assumes exactly an algebraically closed k, a smooth proper integral dimension-one C, a scalar automorphism sigma, and a homeomorphic endomorphism u compatible with sigma. All are present here, with compatibility checked by the displayed local-function equality. It supplies an integral twist, an isomorphic first projection, the unique lift, an injective field map, and precisely v^* beta = u^*. Thus the comparison is not being cited merely for a definition or for a stronger theorem found only in its proof. Its identity-base-change clause also covers n=0.

Step 3 cites def-sc-function-field, read in sec-abelian-varieties, which explicitly identifies the field for an integral curve with its generic stalk, and the absolute Frobenius definition, which gives the sheaf map on every open. A germ is represented by a local section by the definition of stalk, so the written germ computation gives the required map on every field element, without an uncited fraction-field or tensor comparison. Step 4 uses the comparison node's explicitly stated field isomorphism beta and composition equality. Surjectivity of beta and the power formula from step 3 give both inclusions, written separately. Its citation again uses the statement, not its proof. All quotes in citations.json are verbatim from the opened node statements.

For small cases I checked n=0, where sigma, u, v and the field map become the identity; C=P^1 over an algebraic closure of F_p, where the image is k(t^(p^n)); and p=2,n=1, where the same calculation gives k(t^2). I also checked why the algebraically closed base condition matters: over F_p(s), the relative Frobenius image contains constants s, which need not lie in K^p, so the scalar automorphism argument must not be applied there. The statement includes algebraic closedness, so this causes no correction.

Against delivery-errors B-E: there are no new statement-only nodes to relabel or duplicate; all non-elementary content is the existing twist comparison; elementary steps carry explicit root, germ and two-inclusion arguments. No step exceeds 2000 characters. The statement's objects and hypotheses were preserved, proof_deps is the exact union of uses, the comparison is in the same unit, and no forbidden SGA source is used. No Lean was written and no compiler, Lake or local DAG/preflight check was run. The first dry run requested a longer quotation for def-sc-function-field; I replaced the short formula with its full integral-curve identification clause. The required server dry run is the remaining validation before push.

## Repair of the returned promotion refusal

The return said the approved side completion had not been promoted to the live DAG and required rebasing, re-reading changed citations, and adjusting the split. I retained the previously delivered four-step proof, all source references, the original review above, and both inherited and logged Q156 searches. I compared the sandbox item with the current read clone: the live item is unsplit with empty proof and proof_deps, and there is no released repair note. Its statement, stmt_deps, provenance, chapter, and unit are unchanged. I rebuilt the sandbox item from that current node and overlaid the retained stage-1 delivery fields, so current metadata is preserved.

I re-opened all five proof-dependency statements. The ring-Frobenius, algebraic-closure, absolute-Frobenius and function-field quotations still occur verbatim. The changed lem-sfb-automorphism-twist-curve-lift is now split and reviewed by L, and adds the generic-point notion citation and the explicit gloss that function-field pullback is the generic stalk homomorphism. Those insertions broke the retained long quotations: the first required dry run reported exactly the two outdated quotes for steps 2 and 4. I replaced both with the current complete statement. The change strengthens the precision of the comparison used here: its hypotheses still are algebraically closed k, a smooth proper integral dimension-one curve, a scalar field automorphism, and a homeomorphic u satisfying au=sa. Step 1 constructs precisely that automorphism and step 2 verifies precisely that compatibility. I updated step 2 to explicitly say smooth proper integral and generic-stalk pullback, matching the revised comparison; it still uses only that node's statement. Step 3's germ computation therefore computes the same pullback used in the comparison, and step 4 still uses its field-isomorphism and composition clauses. No new lemma or hypothesis is needed.

For this repair I read again Stacks varieties.tex, labels definition-absolute-frobenius (03SM), lemma-frobenius-endomorphism-identity (0CC7), and remark-n-fold-relative-frobenius (0CCG), curves.tex lemma-inseparable-deg-p-smooth (0CCY), and fields.tex lemma-algebraically-closed (09GR). The direction of the base change and all local power formulas agree. The proof includes n=0 explicitly; for P^1 and p=2 its image remains k(t^(p^n)), and an imperfect base such as F_p(s) is excluded by the algebraic-closedness assumption. I repeated the project-source attachment search, finding no exact declaration, and read the retained search log instead of repeating unchanged Mathlib questions. There are still no new nodes, and no step exceeds 2000 characters. The B-E checks above continue to apply. This is a repair of the retained proof and citation evidence against the current DAG, rather than an unchanged re-push.
