# Q87: lem-sfb-equivariant-root-commutator-support

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-equivariant-root-commutator-support.json`: statement, split into six explicit elementary steps; no Mathlib match.
- `citations.json`: eleven verbatim statement excerpts, one for every cited node in every proof step.
- `searches.jsonl`: actual launcher search records. The original item's search history is retained, and searches run for this delivery are appended to its `mathlib_searches`.
- `report.md`: this report. `write_split.py` is a sandbox-only preparation script and is not a DAG delivery file.

New nodes: 0. New Mathlib leaves: 0. The item already assumes the difficult positive-root coordinate theorem. Its remaining argument is an explicit calculation with universal elements, the reduced-root condition and two specified free coefficient bases. Making any of those two-line calculations into a node would violate the elementary-node rule.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact item tag, root subgroups, root groups, root commutators and pinning found no declaration stating this result. The Chevalley source hits there concern constructible images and related scheme theory, not reductive root groups. No declaration with an unfinished proof was treated as an attachment.

## WANTED

WANTED: Brian Conrad, *Reductive Group Schemes*, archival `literature/conrad-reductive-group-schemes.pdf`, Proposition 5.1.14 and proof, printed pp.145--146, for lem-sfb-equivariant-root-commutator-support. I read the [author's PDF](https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf) online, especially the proof across printed pp.145--146, and Theorem 5.1.13 immediately before it. The PDF is not present locally. The expanded universal-element argument is accordingly marked `proof_origin.by = agent`; no document was downloaded or repository file written. No Stacks tag states this reductive-group commutator result; none has been substituted for Conrad, and no SGA source is used.

## What needed repair

The imported item had no proof. Its statement is correct, including arbitrary base rings, arbitrary order, universal algebra points, and the empty-product conclusion; no statement correction or STATEMENT-DISPUTED entry is needed. The original source and all inherited metadata, including the long inherited blueprint provenance, have been preserved.

Conrad's proof uses coefficients of equivariant two-variable coordinate polynomials. Here the ordered product is already an explicit hypothesis, so I take its inverse at the universal point over A[X,Y]. This gives actual polynomials without invoking any field-valued density assertion, finite-dimensional torus representation theorem, quotient existence theorem, or scheme-theoretic factorization inferred merely from pointwise support. At the universal torus point the calculation takes place in A[M][X,Y]; coefficient projection in the free group-algebra basis works with nilpotents and small residue characteristics. The differential and reductivity assumptions are consistent but are not needed after the item's stronger coordinate hypothesis is supplied.

The item has `blueprint.from.node = null` on the live repository; `tools/blueprint_refs.py ancestor` confirms that its inherited created-item chain reaches no imported blueprint node. I did not invent an ancestor or change this protected provenance. I read the current `literature/blueprint/latest/` direct-images statement/proof, paragraph (3), and the recorded chapter/unit. This calculation is a subordinate prerequisite on the inherited root-calculus branch, not a change of the constructibility route or its chapter. Blueprint searches for `commutator`, `equivariant root`, `positive root` and `diagonalizable` found no equivalent imported theorem.

## Not duplicates

No new node is proposed. I nevertheless read the statements of `lem-sfb-chevalley-nonopposite-exponential-commutator`, `lem-sfb-chevalley-unipotent-polynomial-coordinates`, `lem-sfb-quasifinite-root-map-rigidity`, `lem-sfb-unitriangular-coordinate-filtration`, and the parent `lem-sfb-split-root-subgroup-weyl-calculus`. The first is a commutator formula for a specified rational Lie-algebra representation with an integral stable lattice and a height-refining order; it does not state the present arbitrary-ring realization with every order. The parent uses this item, so citing it here would create a cycle. Field or finite-projective torus-weight decomposition nodes would add hypotheses or require a separate specialization argument; this proof instead projects the explicitly defined group-algebra coefficients. None of these nodes is used by borrowing its proof.

## Mathlib searches

I ran leanfinder, loogle, grep and leansearch through the mandated `msearch.py`, and then a second semantic phrasing and a second grep in AlgebraicGeometry. Queries and tool names in the item are verbatim from the resulting `searches.jsonl`. No unavailable service was recorded as absence. All six searches succeeded.

The semantic hits are Geck Lie brackets, root-chain combinatorics and positivity in abstract root pairings. I inspected the local source of `RootPairing.GeckConstruction.lie_e_lie_f_apply` in `Mathlib/LinearAlgebra/RootSystem/GeckConstruction/Basic.lean:315` and `RootPairing.GeckConstruction.lie_e_f_same` in `GeckConstruction/Relations.lean:140`; they are Lie-bracket identities, not polynomial group-scheme commutator coordinates. `commutatorElement` and its defining identity, read in `Mathlib/Algebra/Group/Commutator.lean:30`, only define the four-factor group expression. Loogle's root/commutator query has no hits. The AlgebraicGeometry grep finds Chevalley constructibility imports/theorems. None supplies the item or a one-line specialization of it.

## Review by Q87

I read Conrad Proposition 5.1.14 and its proof online and compared its hypotheses with the item clause by clause. The source assumes nonopposite roots, uses an ordered positive-root product and then proves the polynomial support. Here the nonopposite condition follows from positivity and distinctness, and the ordered product is an explicit hypothesis. We are not proving the existence of those coordinates again. There are no new nodes requiring additional sources. I read the full statements of all five existing nodes actually cited, rather than using properties from their proofs, and checked each quoted substring against those statements.

Step 1 uses `def-sfb-pinned-split-root-realization` for the reduced-root condition and the finite free character lattice. If b were proportional to a over Q, reducedness would force b = a or b = -a, both excluded. This proves injectivity of (i,j) -> ia+jb, finiteness of the index set, and its inclusion in Sigma. Extending an enumeration is a finite-set operation; it requires no assertion about permuting noncommuting factors.

Step 2 uses `def-weil-closed-immersion` for its affine quotient description and `def-weil-affine-spectrum` for the correspondence between the quotient algebra and the closed image. Thus each p_c is an identification with its own image, and the product bijection is exactly the hypothesis of the item. The commutator belongs to U_Sigma because this image is assumed to be a subgroup, not merely a subscheme. `def-weil-pbc-mv-polynomial-ring` gives the actual ring A[X,Y] and its evaluation maps. Inverting the given bijection at this one universal ring defines h_c, and applying evaluation to the factorization proves its identity for every algebra. No non-elementary existence or naturality lemma is hidden here: all maps are the given morphisms, whose product formula commutes with algebra maps, and inverse coordinates commute by uniqueness.

Step 3 uses `def-sfb-ring-diagonalizable-group` for T = Spec A[M] and the monomials e_m; `def-weil-pbc-mv-polynomial-ring` supplies the polynomial coefficient extension. I checked that the inclusion A[M] -> A[M][X,Y] really is a torus point: it is an A-algebra homomorphism, and e_m is a unit with inverse e_{-m}. Conjugating a product of the given p_c factors multiplies the c-coordinate by c(t), by the item's own equivariance hypothesis. Applying uniqueness yields the written polynomial identity. This is the action of the entire torus on all algebra points, not its Lie algebra or just its A-valued points.

Step 4 uses the coefficient description in `def-weil-pbc-mv-polynomial-ring`. Both axes are evaluated as polynomial identities, over A[X] and A[Y], not merely as functions on A. A group homomorphism takes zero to the identity and minus to inverse. Therefore both axis coordinate vectors are zero by uniqueness, which annihilates precisely every coefficient with one exponent zero, including the constant coefficient.

Step 5 uses precisely the polynomial coefficient description and the group-algebra basis/multiplication in `def-sfb-ring-diagonalizable-group`. It compares X^i Y^j coefficients, then the e_{ia+jb} coefficient. If the two character indices are distinct, the latter coefficient is d on one side and 0 on the other. No nonzero-divisor, reducedness, invertible integer, faithful-flat character argument, or field base change is needed. This direct two-stage coefficient calculation is elementary and is written out; it is not a new black-box equivariant-polynomial lemma.

Step 6 uses the independence obtained from the pinned-root definition and the evaluation formula in the polynomial-ring definition. For each root there is at most one surviving pair, so we obtain C_{i,j} in A. Zero coordinates insert the identity factor. Removing those factors retains exactly the prescribed order selected before any calculation. Evaluation maps the constants from A to R and proves all of the requested clauses. An empty index set gives a commutator equal to 1, which is equivalent to commutation by multiplying by the inverse factors.

I checked delivery-errors B through E in both copies of those sections. There are no new nodes, hence no underspecified objects, bogus leaves, unsearched new statements, duplicates, or relabelled clauses. Every proof dependency is one of the eleven cited (step,node) pairs in citations.json, and the union agrees with proof_deps. The item is not cited in its own proof; neither is its parent. No other-unit theorem is used, so no tool-use declaration is necessary. All six steps are below 2000 characters (the longest is 771); each performs one explicitly displayed definition-level calculation or finite-set operation. The proof's elementary flags refer to these actual calculations, not to an omitted appeal to a 'standard' theorem.

For edge cases I checked empty roots and rank-one root systems: there are no distinct positive pairs, so the assertion is vacuous. For A1 x A1, I_{a,b} is empty and every coordinate is eliminated. In type A2 the elementary matrix example p_a(x)=1+xE12, p_b(y)=1+yE23 gives commutator 1+xyE13, agreeing with i=j=1. This calculation still holds over F2 and F2[epsilon]/(epsilon^2). More generally, the coefficient extraction remains valid over Z/4, over a nonreduced ring, and over a product such as Z x F2, because it uses free bases rather than values at geometric points. The constants may vanish in small characteristic, which the statement permits; no unit assertion about them is introduced. For any A-algebra R, including the zero algebra if allowed, the same evaluation identity applies. No hidden Noetherian, domain, connectedness, or characteristic-zero hypothesis entered the proof.

## Unfinished work

None in this stage-1 split. Independent maintainer review remains the prescribed next review step after successful preflight and push.
