## Worker report

Files written:
- `dag/nodes/sec-trace-formula/lem-trf-geometric-reducedness-separable-scalar-restriction.json`: existing statement retained verbatim; two-step assembly now 2430 characters.
- `dag/nodes/sec-trace-formula/lem-trf-tensor-diagonal-unit-hom.json`: statement, unsplit; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-tensor-diagonal-evaluation-hom.json`: statement, unsplit; no Mathlib match.
- `citations.json`: verbatim statements for every citation of both assembly steps.

Attachments: none. The recorded `Algebra.forall_isReduced_tensorProduct_iff_of_isSeparable` in `lean/Sheaf/RingTheory/GeometricReducednessSeparableScalarRestriction.lean` ends in `sorry`. Searches under `lean/WeilConjectures/` for the blueprint tag, declaration and geometric-reducedness notions found no exact completed declaration. Nothing was compiled or written in Lean.

WANTED: none.

This repairs the single batch5 return: the old proof has 1057 and 1980 character steps and contains a substantial tensor identification inline. No earlier sandbox node, report or searches existed (only dispatcher marker files). I copied the current shared item, whose two steps match those lengths, preserved its statement, citations, searches, sources and metadata, and saved the original argument as `returned-proof.json`. The new nodes are the two independent well-defined ring-map constructions behind the displayed identity of Stacks 0C2Y. Neither assumes reducedness or separability, neither proves either direction of the item, and neither states the isomorphism or the original equivalence. Their statements have comparable sizes, 876 and 903 characters, and are delivered statement-only with empty proof/dependency lists. The parent retains the inverse check. Its full first direction and final localization argument remain intact; nothing is replaced by an unexplained identification.

## Sources and searches

I read `literature/stacks-project/algebra.tex`, label `lemma-geometrically-reduced-over-separable-algebraic` (0C2Y), its two proof paragraphs and displayed identity, label `lemma-separable-algebraic-diagonal` (0C2X), and the adjacent reduced-base-change (034N) and separable-extension-preserves-reducedness (030U) arguments. Both new statements are explicitly marked as agent generalizations of the two maps in the 0C2Y identity, from fields to arbitrary commutative rings and algebras. This uses only the balanced tensor construction and makes no new claim about geometric reducedness over general rings. I read the chapter and unit records; this is below the existing scalar-restriction input and does not change their routes. The inherited ancestor is `lem-trf-local-term-locality`; `blueprint_refs.py ancestor` confirms it, and both new via lists begin with this item followed by its inherited chain.

Before creating either node I searched all DAG nodes by 0C2Y, 0C2X, balanced, diagonal/tensor and tensor-square formulas, and searched the whole imported blueprint with `blueprint_refs.py search` for balanced, 0C2Y, 0C2X, tensor square, tensor/multiplication and diagonal tensor. Hits about coefficient sheaves, derived tensor and finite-field diagonal summands do not assert either ordinary ring map for arbitrary commutative algebras. In particular the finite-field summand lemma cannot supply these maps for arbitrary field extensions. No blueprint same_as was found.

For each new node `msearch.py` ran LeanFinder, Loogle, grep and LeanSearch, plus a second semantic phrasing. Exact queries/results are recorded in `searches.jsonl`, the search output files, and the nodes' mathlib_searches. LeanSearch returned rate-limit unavailability, recorded as unavailable. LeanFinder and Loogle returned general `Algebra.TensorProduct.lift`, `map`, `mapOfCompatibleSMul`, multiplication maps, cancelBaseChange and pushout constructors. I read Maps.lean 90–110, 148–171 and 313–350, Basic.lean 762–795, and IsTensorProduct.lean 688–709. These require the relevant scalar-compatible algebra maps/CompatibleSMul instances as input: establishing precisely those two balancing conditions is the work split here. They do not state the proposed maps under only the proposed hypotheses as a one-line specialization. `Algebra.IsPushout.tensorProduct_tensorProduct` constructs the base-changed pushout square, not this diagonal comparison. I also reread GeometricallyReduced.lean and its explicit TODO on all-field-extension reducedness, preserving the old item's searches rather than repeating them.

## Arguments preserved for the new tasks

These are handoff arguments in the report, not proofs hidden inside the statement-only children.

For `lem-trf-tensor-diagonal-unit-hom`, put Q = D tensor_R L and use the explicit actions in its statement. The k-bilinear rule (b,c) maps to (b tensor c) tensor 1 descends over L because, for lambda in L,

$$
(\lambda b\otimes c)\otimes1
=\psi(\lambda\otimes1)(b\otimes c)\otimes1
=(b\otimes c)\otimes\lambda
=\psi(1\otimes\lambda)(b\otimes c)\otimes1
=(b\otimes\lambda c)\otimes1.
$$

After this balancing calculation, the tensor universal property produces alpha. It preserves the unit and products of pure tensors, and distributivity gives multiplicativity for sums of pure tensors. Uniqueness follows because pure tensors generate additively. This is the first construction and its scalar-action verification, not a copy of either implication of the item.

For `lem-trf-tensor-diagonal-evaluation-hom`, first construct q:D -> B tensor_L C from the two factor inclusions, sending b tensor c to b tensor c. Verify q(psi(lambda tensor lambda-prime)x) = lambda lambda-prime q(x); expand x and the R coefficient into sums of pure tensors, then use L-balancing in the relative tensor. Thus (x,c) maps to c q(x) is R-balanced for the multiplication action on L. Its induced map beta has the stated formula. The product calculation c q(x) c-prime q(x-prime) = cc-prime q(xx-prime) and the unit formula prove that it is a unital ring map. Uniqueness follows from additive generation by the double pure tensors. This is the second construction, independent of alpha; it does not presuppose the inverse relation.

The inverse checks are retained in the parent: beta alpha fixes each relative pure tensor, and alpha beta sends (e tensor a) tensor c to (ce tensor a) tensor 1, equal to the original double pure tensor by balancing with c tensor 1 in R. This accounts for every equality and multiplicative assertion in old step 2. The old first-direction empty-transcendence-basis argument, swaps, 030U, 034N and cancellation formulas are preserved verbatim in step 1. The old positive-power nilpotent-fraction argument and the 0C2X/base-change applications are preserved in step 2.

## Not duplicates

lem-trf-tensor-diagonal-unit-hom vs lem-trf-geometric-reducedness-separable-scalar-restriction: same source tag 0C2Y, but this is one ring map for arbitrary commutative k-algebras L,B,C, without field, separability or reducedness assumptions; it states no inverse and no reducedness equivalence.
lem-trf-tensor-diagonal-evaluation-hom vs lem-trf-geometric-reducedness-separable-scalar-restriction: same source tag 0C2Y, but this is the opposite evaluation ring map for arbitrary commutative algebras, with its double-pure-tensor formula; it states no inverse or reducedness implication.
lem-trf-tensor-diagonal-unit-hom vs lem-trf-tensor-diagonal-evaluation-hom: the former descends B tensor_L C into the diagonal base change, the latter evaluates the diagonal base change; different domains, balancing requirements and characterizing formulas, with neither assuming the other.

## Review by NF

I checked the repair against B–E with the original and new node files and algebra.tex open. The item's statement is exactly the 0C2Y assertion with the all-extension-fields definition spelled out; I did not change any hypothesis or conclusion. Both new nodes introduce k,L,B,C,R,D, their two structure maps, all tensor ring operations and the zero-algebra case. Each statement has just one claim about a uniquely specified map, no proof steps or proof sketch. Their only statement dependency, the tensor-product definition, supplies bilinearity, the universal property and additive generation; their ring operations are stated inline. They have no dependency on the parent or on one another.

Step 1 still cites the separable-algebraic, separably-generated and transcendence-basis definitions: their actual statements show the empty family is a separating transcendence basis because k1/k is algebraic and separable. The 030U node explicitly allows arbitrary separably generated K and reduced S, so applies with K=k1 and S=E; it does not demand finite degree. The 034N node explicitly applies to every reduced base algebra, so applies over k1 with R=E tensor_k k1 and A satisfying (2). The cancellation node explicitly gives a tensor isomorphism with the needed scalar tower and inverse; swap both factors to get the written formula. I opened each cited node and checked those exact clauses, rather than relying on the Stacks tag alone. Scalar swaps preserve multiplication directly on pure tensors. The inherited generic 030U tool use remains the same.

Step 2 uses the new unit/evaluation statements exactly for the maps and formulas they assert, with L=k1, B=E, C=A; it does not use an unstated inverse theorem or read a child's proof. The inverse check uses the explicit R-action and additive generation. The 0C2X node explicitly makes multiplication R -> k1 a localization for possibly infinite separable algebraic k1/k. The localization-base-change node explicitly applies to ANY ring map R -> D and gives localization at its image subset, matching psi here; no field or injectivity is demanded of D. Finally the positive-exponent fraction calculation is written out, including the annihilating multiplier, so there is no uncited reduced-localization assertion. Each cited statement is copied verbatim into citations.json. Both steps remain below 2000 characters, total 2430, below the return's 3000 bound.

Small cases: L=k gives both maps the identity after tensor-unit identification. B=0 or C=0 makes source and target zero, where the unique unital map is valid. A nonreduced L or B is also allowed: the balancing equalities use no cancellation or reducedness. A noninjective k -> L introduces no difficulty: the action formulas use the structural homomorphism only. For the parent I checked k1=k, A=0, A=k1 and infinite algebraic separable k1/k; none is discarded. Separability cannot be dropped from the parent: for a nontrivial purely inseparable k1/k, A=k1 is geometrically reduced over k1 but k1 tensor_k k1 has a nonzero nilpotent. The new ring-map assertions still hold in that case, confirming that they isolate the tensor identity rather than assuming its reducedness consequence.

The return's request to spread the work is repaired by two independent unsplit tasks of comparable statement size, not by moving an implication wholesale or merely shortening the old text. All old arguments are either retained verbatim, retained explicitly in the parent, or assigned to the precisely characterized child map and preserved above for its next worker. No source or statement dispute arose. No SGA source was used. No work is left unfinished apart from the intentionally statement-only child proofs.
