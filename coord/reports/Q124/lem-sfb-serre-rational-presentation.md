# Q124: lem-sfb-serre-rational-presentation

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-serre-rational-presentation.json`: item, statement retained; eight-step proof, status split.
- `dag/nodes/sec-six-functors-basics/lem-sfb-serre-graded-triangular-quotient.json`: new statement-only node, unsplit; Mathlib defines the quotient but has no triangular-decomposition theorem for it.
- `dag/nodes/sec-six-functors-basics/lem-sfb-integrable-sl2-reflection-automorphism.json`: new statement-only node, unsplit; no Mathlib match for the locally nilpotent sl2 reflection theorem.
- `citations.json`: verbatim statement quotations for every node use in every item step.
- `searches.jsonl`: actual search-command records; the item's inherited searches are retained, with this run's additional evidence. Auxiliary extraction and writing scripts remain only in the sandbox.

Two new nodes, zero new Mathlib leaves. No Lean written or compiler used.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint tag and for Serre, Chevalley, root-system, Cartan, RootPairing, and sl2 terminology. No project declaration proves this item or either new node. Existing Mathlib declarations are not project attachments.

## Wanted literature

WANTED: N. Bourbaki, Lie Groups and Lie Algebras, Chapters 7–9, Chapter VIII §4 no.2 (and §4.3), triangular decomposition of the Weyl presentation and its positive/negative Serre ideals, for lem-sfb-serre-graded-triangular-quotient.

WANTED: J.-P. Serre, Complex Semisimple Lie Algebras, Chapter VI, appendix (the reference called Serre 1966, VI by Milne), direct Serre presentation proof and reflection argument, for lem-sfb-serre-graded-triangular-quotient and lem-sfb-integrable-sl2-reflection-automorphism.

Milne's PDF is present and was read. These two further books are not present in the named literature tree. They are requested here as required by the read-only worker brief; no literature files were changed or downloaded. The item is marked proof_origin.by = agent because its expanded arguments go beyond Milne's abbreviated first proof. New unsplit nodes make no claim to a completed proof.

## Problems found and corrections

No statement dispute: the imported item is correct, including the empty-root-system convention. It already corrects the errors in Milne's p.504 display. Read literally, Milne prints [X_i,X_i]=H_i, repeats [H_i,X_j] in the Y relation, omits its negative sign, uses n(i,j)+1 rather than 1-n(i,j) in the adjoint exponent, and prints J_j in the negative Serre relation. In rank one the first typo would kill H, E and F, so it cannot be the intended construction. The item's relations and Mathlib/Algebra/Lie/SerreConstruction.lean:17–27 agree on the corrected formulas. No target statement was changed.

The source's conclusion that the quotient is semisimple with the required roots cannot itself serve as the only new dependency: that would merely rename this item. Instead the two new inputs concern arbitrary generalized Cartan matrices and arbitrary locally integrable sl2 triples, respectively. The item supplies the finite-root-type height descent, root multiplicities, normalized coroot brackets, solvable-ideal exclusion and self-centralizing Cartan calculation.

## Not duplicates

lem-sfb-serre-graded-triangular-quotient vs lem-sfb-serre-rational-presentation: the new lemma is about grading and positive/negative free Lie quotients for arbitrary generalized Cartan matrices, even singular or affine ones; it asserts no finite dimension, prescribed finite root system, or semisimplicity.

lem-sfb-serre-graded-triangular-quotient vs lem-sfb-kostant-integral-pbw: Kostant's lemma assumes an already constructed split semisimple rational Lie algebra and concerns an integral basis of its associative enveloping algebra, not injectivity and triangular decomposition of a presented Lie algebra.

lem-sfb-serre-graded-triangular-quotient vs lem-sfb-chevalley-root-normalization: the latter assumes an already split semisimple algebra and normalizes root-vector bracket constants; it does not identify the free Serre quotient.

lem-sfb-serre-graded-triangular-quotient vs lem-sfb-chevalley-admissible-representation: the latter constructs full Chevalley and representation/lattice data; it uses this item and cannot be a dependency for its quotient theorem.

lem-sfb-serre-graded-triangular-quotient vs lem-sfb-root-datum-realization: the latter realizes an algebraic root datum as a group scheme and depends upstream on this Lie presentation input.

lem-sfb-serre-graded-triangular-quotient vs lem-sfb-rational-highest-weight-modules: the latter assumes a finite-dimensional split semisimple algebra and constructs simple highest-weight representations, not a grading of an arbitrary presented Lie algebra.

lem-sfb-integrable-sl2-reflection-automorphism vs lem-sfb-serre-rational-presentation: this input assumes a locally nilpotent sl2 action in an arbitrary rational Lie algebra, without any root system, finite dimension or Serre presentation; its conclusion is an explicit automorphism and weight-space isomorphism.

lem-sfb-integrable-sl2-reflection-automorphism vs lem-sfb-chevalley-root-normalization: root-vector normalization in an already semisimple Lie algebra does not supply exponential automorphisms in a potentially infinite-dimensional locally nilpotent action.

lem-sfb-integrable-sl2-reflection-automorphism vs lem-sfb-kostant-integral-pbw: an integral associative enveloping-algebra basis does not assert this reflection automorphism or its action on arbitrary weights.

lem-sfb-integrable-sl2-reflection-automorphism vs lem-sfb-simple-root-reflection-generation: generation of a finite orthogonal reflection group is a combinatorial assertion on V, not the construction of Lie automorphisms lifting its generators.

The DAG was searched globally by statement/title and by Serre presentation, triangular decomposition, generalized Cartan, locally nilpotent, nonempty_base, exponential and source place 23.63. Read the existing chamber, rational-base, crystallographic-positive-base, root-lattice-embedding and simple-reflection-generation statements. The first two are reused. The lattice-embedding node needs an ambient lattice and is not used. The positive-base node proves only linear independence, not existence of a base. The blueprint_refs searches for Serre presentation, root system, Lie algebra, triangular decomposition, Weyl, exponential and generalized Cartan found no same-statement blueprint node. The latest blueprint has no item tag. Ancestor reports blueprint.from.node = null for this inherited chain; the existing provenance is retained and the item is prepended to each new node's via list. No SGA source is used.

## Review by Q124

I read Milne Appendix C.19–C.22, printed pp.611–612, C.1–C.3 on reflection conventions and uniqueness, and Section 23h, Theorem 23.63 first proof, pp.503–504, together with its rational-field extension on p.508. I compared the source against the entire item statement. The proof is for the actual rational free-Lie quotient; it does not descend an unspecified complex Lie algebra and does not change which simple-root base is allowed. I read both cited existing root-theory statements and the two Lie definition statements. I also read the relevant Mathlib definitions and search candidates, not just their search snippets.

Step 1 uses finite faithfulness on the spanning root set to get a finite reflection group, and writes its averaged rational positive form explicitly. Orthogonality of the two reflection eigenspaces yields the precise coroot formula. This verifies dual spanning, coroot injectivity, equivariance and real reducedness needed later; none is silently included in the definition of a root system. The empty case is disposed of before any nonempty-base argument.

Step 2 uses the chamber node's actual bijection from bases to components. A generic point is exhibited by a polynomial curve avoiding finitely many hyperplanes, so the component exists; no hidden existence theorem for chambers is invoked. The roots remain rational, making the real basis rational by its determinant. For ANY subsequently fixed base I use lem-sfb-root-base-rational-integral-spans, whose statement explicitly concludes that its simple coroots form a rational basis. Its perfect pairing, both spanning conditions, reducedness, integral pairings and simultaneous root/coroot permutations were all checked against step 1. Thus no coroot-basis conclusion is taken from the weaker positive-base node.

Step 3 checks the off-diagonal sign from the unchanged coefficient 1 of alpha_j in s_i(alpha_j), and checks symmetric zero entries from B. Those are exactly the hypotheses of the new graded quotient node. Its statement supplies independent H, sign-pure degrees, the simple degree spaces, and absence of higher pure simple degrees. Induction by Jacobi gives the displayed eigenvalue on every bracket. The previously proved dual-basis isomorphism makes distinct degrees distinct actual adjoint weights, an issue that would fail for a singular Cartan pairing without the finite-root-type hypotheses.

Step 4 checks local nilpotence on EVERY generator, including F_i where the bound is three. The binomial derivation formula explains why these generator bounds imply local nilpotence on Lie words, without claiming a uniform bound on the whole algebra. The reflection node requires precisely local nilpotence and alpha_i(H_i)=2, both now supplied. Its actual weight-isomorphism and Cartan-action formulas are what this step uses.

Step 5 uses the quotient node's sign restriction and its exclusion of n alpha_i for |n|>1, and the reflection node's weight isomorphisms. The argument is induction on a positive integer height; at each genuine descent the reflected vector still has another positive coefficient, so cannot become negative or zero. The positive form ensures a descending reflection. The same computation on the given finite root set proves the converse inclusion. This proves root multiplicities and finite dimension rather than assuming them in a new node. The step is marked non-elementary and explicitly cites both structural inputs; its internal height calculation is written out.

Step 6 uses the reflection node again to lift a word of simple reflections and calculates its dual action on h. Equivariance of c_alpha from the rational invariant form identifies the image of H_j with the GIVEN c_beta. Bracket preservation then supplies the opposite-root sl2 triple and its normalization beta(h_beta)=2. Merely knowing a root-space dimension would not establish this clause; the argument explicitly checks it.

Step 7 uses the Lie-algebra definition's actual derived-series definition and the semisimple definition's exclusion of solvable ideals. Polynomial projectors onto finitely many distinct rational weights preserve the ideal. A root vector in it forces the complete nonzero perfect sl2 triple into it and then into every derived term, a contradiction. If only the zero-weight part remains, brackets with the simple E_i kill it by the dual-basis isomorphism. This direct calculation uses no unproved general radical theorem. Step 8 proves maximal abelianness from the displayed weight decomposition by computing the centralizer, not by treating a definition of Cartan subalgebra as a theorem.

For the new triangular node I checked I empty (zero algebra), A=(2) (three-dimensional sl2), a zero off-diagonal block (commuting factors), A2 and B2 (positive Serre relations have lengths 2 or 3 as appropriate), and the affine matrix [[2,-2],[-2,2]]. The affine example explains why the new node deliberately does not assert finite dimension and why its H_i cannot be identified with independent weight functionals in an arbitrary application. The pure multiple assertion follows from the free Lie algebra on one letter and does not require a finite root system.

For the new reflection node I checked the actual 2x2 sl2 triple: w(e)=-f, w(f)=-e and w(h)=-h, so the chosen middle minus sign and weight formula are correct. A central abelian summand is fixed, as predicted by alpha(t)=0; no assumption of complete reducibility or finite dimension has been smuggled in. Local nilpotence makes each exponential finite on each vector, but is strictly weaker than Mathlib LieDerivation.exp's global nilpotence, so that hit is not declared a match. The new statement includes all its objects and assumptions, has no proof sketch or proof dependencies, and uses the existing Lie definition for brackets and adjoint action.

I checked B1–B10: both new nodes are self-contained statement-only nodes; all structural notions are defined inline or by def-wf-lie-algebra; TeX is singly escaped after JSON decoding; this Lie-theoretic source has no applicable Stacks tag; no unattested Mathlib match is asserted; every recorded query is an actual msearch.py invocation, with its original result record and verdict. Queries were rephrased before concluding absence. Base-existence queries found genuine Mathlib results, but the existing chamber and rational-base nodes already cover those needs and no redundant leaf was created. I checked C1–C8 by the statements and the verbatim quotations, and D1–D5 by verifying that neither new input is a clause-only replacement or circular dependency. Source errors are recorded above. E1–E7 are addressed by the explicit hypotheses and edge cases in this review. Every proof step is below 2000 characters. No unit or chapter file changed, and all proof statement dependencies remain in the item's unit or are definition leaves.

The first dry run flagged the phrase “as in the item” in step 2 as a self-containment failure. I replaced it by an explicit description of the arbitrary rational simple-root base. I also made the support condition of the triangular node explicit as L(A)_m nonzero, m nonzero, rather than speaking loosely of a nonzero homogeneous degree.

## Unfinished work

No part of the assigned one-level split remains unfinished. The two new unsplit nodes are the explicit follow-up items prescribed by stage 1. The further literature requested above is needed for their subsequent splits.
