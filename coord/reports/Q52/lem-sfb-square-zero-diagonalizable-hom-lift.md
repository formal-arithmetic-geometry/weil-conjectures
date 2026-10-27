## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-square-zero-diagonalizable-hom-lift.json: item, statement preserved, split into four steps.
- dag/nodes/sec-six-functors-basics/lem-sfb-square-zero-hom-regular-defect.json: statement, unsplit, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-diagonalizable-regular-two-cocycle.json: statement, unsplit, no Mathlib match.
- citations.json: verbatim statement excerpts for every step/node citation.

Two new nodes, zero Mathlib leaves. No Lean written or compiled. No repository or launcher files changed.

## Attachments

None. Searched lean/WeilConjectures by the item id and the diagonalizable, homomorphism lifting, cocycle and infinitesimal terminology. The existing group-scheme tangent and invariant-coefficient files do not state this lifting assertion. No candidate for an exact attachment was found.

## Literature wanted

WANTED: Conrad, Reductive group schemes (2014), Appendix B.2, printed pp.283-287, https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf, local archive literature/conrad-reductive-group-schemes.pdf, for the item and both new nodes. Read the source online, including Remark B.2.4, Proposition B.2.5 and the proof of Corollary B.2.6. It is absent from the local literature inventory. As instructed, no download or inventory edit was made. The item's proof is marked agent with its online source, rather than falsely claiming a local document. No SGA source is used.

## What was wrong and what changed

The imported statement is sound. The source refers to two genuinely different inputs, rather than a formal-smoothness assertion alone: linearization of the multiplicativity defect and vanishing of its regular cohomology class. The item had no proof; the split now constructs a scheme morphism and corrects it, instead of moving the existence conclusion into a new node.

The kernel comparison in the new defect node is deliberately stated only on flat A-algebras. In general J tensor_A R need not inject into R for a non-flat test algebra, so a blanket identification with the kernel on all A-algebras would be false. The coordinate ring A[M] and every tensor power are free over A, which is exactly enough to construct the regular defect and correction on universal points. This restriction is on an auxiliary comparison, not a new hypothesis on A, M or the item.

The source uses quasi-coherent modules; the regular-cochain node writes its content as an explicit module coaction and cocycle identity. This prevents accidental substitution of ordinary cohomology of the abstract group of points, which does not provide a regular cochain.

## Searches and reuse

Before creating nodes, searched all dag/nodes by diagonalizable, Hochschild, regular cochains, two-cocycles, B.2.4, B.2.5 and B.2.6, inspecting candidate statements. Ran tools/blueprint_refs.py ancestor on the item, and search on diagonalizable, Hochschild, square-zero, cocycle, defect, B.2.4 and B.2.5. No blueprint node states either new lemma. The ancestor tool reports blueprint.from.node = None, consistent with the inherited long created-node chain; retained this and prepended the item to the new nodes' via lists. Checked latest blueprint text, not an older snapshot.

For each new node ran two differently phrased LeanFinder queries, Loogle, source grep and LeanSearch through msearch.py. Read all hits and the relevant Mathlib source: RepresentationTheory/Homological/GroupCohomology/LowDegree.lean, RingTheory/Derivation/ToSquareZero.lean, and Algebra/Lie/Extension.lean. The first is abstract-group cohomology with arbitrary function cochains; the second concerns algebra-map lifts and derivations; the third concerns Lie algebra extensions. None gives the regular scheme cochains or their diagonalizable vanishing. The source grep's sole Hochschild hit is a TODO mentioning the Hochschild-Serre spectral sequence. Repeated the item's inherited searches under Q52 so the delivery's searches.jsonl independently records them. Every mathlib_searches entry is taken from an actual msearch.py log entry, with its literal query and results.

## Not duplicates

lem-sfb-square-zero-hom-regular-defect vs lem-sfb-group-space-square-zero-kernel-module: the existing node identifies the kernel at one affine thickening, but does not give the adjoint representation on the coefficient module, regular multiplicativity cocycle, or correction formula for an arbitrary scheme-map lift.
lem-sfb-square-zero-hom-regular-defect vs lem-sfb-group-space-square-zero-difference-additive: the existing node proves additivity of the kernel's difference coordinate, not the regular defect and its cochain variation.
lem-sfb-square-zero-hom-regular-defect vs lem-sfb-split-torus-infinitesimal-conjugacy: the existing node assumes two group homomorphism lifts already exist and proves conjugacy. The new node assumes a scheme morphism lift for an arbitrary flat affine source and gives regular defect formulas, without asserting existence of a homomorphism.
lem-sfb-square-zero-hom-regular-defect vs lem-sfb-square-zero-diagonalizable-hom-lift: the new node neither assumes diagonalizability nor constructs an initial scheme-map lift nor asserts the existence of a homomorphism lift; the item must combine its formulas with two-cocycle vanishing.
lem-sfb-diagonalizable-regular-two-cocycle vs lem-sfb-diagonalizable-representation-weight-grading: the existing node is about finite-dimensional representations over a field; the new node is about two-cocycles for arbitrary modules over any commutative ring.
lem-sfb-diagonalizable-regular-two-cocycle vs lem-sfb-trivial-torus-coherent-weight-decomposition: the existing node concerns coherent linearizations on Noetherian schemes over a field and a torsion-free character lattice; it gives neither the general-ring regular bar complex nor degree-two vanishing for torsion character groups.
lem-sfb-diagonalizable-regular-two-cocycle vs lem-sfb-smooth-diagonal-additive-crossed-vanishing: the existing node is degree one over an algebraically closed field, with smooth source and a closed subgroup of the additive group as coefficient; the new node is degree two, over arbitrary rings, with arbitrary coaction modules and possibly nonsmooth source.
lem-sfb-diagonalizable-regular-two-cocycle vs lem-sfb-split-torus-infinitesimal-conjugacy: the existing node is a conjugacy assertion for supplied lifts of a split torus. The new node is a regular cochain assertion, permits torsion characters, and mentions no thickening or target smooth group.
lem-sfb-diagonalizable-regular-two-cocycle vs lem-sfb-square-zero-diagonalizable-hom-lift: the new node has no smooth target group, thickening or homomorphism lifting problem; it supplies the independent cochain-vanishing input used to correct the multiplicativity defect.

## Review by Q52

I read Conrad Appendix B.2 online: the regular complex and its coefficient convention on printed pp.283-284, Remark B.2.4 on p.285, the defect computations in Proposition B.2.5 on pp.286-287, and the kernel comparison in Corollary B.2.6 on p.287. The two new nodes state these supporting inputs in explicit algebraic terms; neither is the item's existence assertion. I also opened Stacks groupoids.tex lemma-group-scheme-addition-tangent-vectors (Tag 0BF5) and more-morphisms.tex lemma-difference-derivation and lemma-action-by-derivations (Tags 0618 and 04D0) when assessing whether the existing kernel nodes supplied all the required assertions. They do not supply the adjoint regular defect and correction, so they were not falsely cited for those conclusions. These are comparisons of scope, not additional uncited dependencies in the item's proof.

Step 1 uses the actual statement of def-sbc-smooth-morphisms: its affine first-order test gives a global scheme-map lift, with no assumption that the source is smooth. I read this definition, including the quantified affine test, and checked that H_0 is the indicated square-zero affine thickening of H. The basis of the group algebra identifies the reduction coefficientwise, and products of coefficients in J vanish. Its tensor powers are free; tensoring an injection with a free module is the direct sum of that injection. These elementary facts verify flatness of the coordinate test algebras, without invoking a theorem on a group of rational points.

Step 2 cites the whole regular-defect node, specifically its adjoint coaction and explicit regular cocycle equation. The supplied f has exactly the required reduction u_0; C is flat by step 1 and G is smooth by the item's hypothesis. The cotangent module at the identity is defined in the new node by derivations, the tensor product has its definition node, and all group operations are specified inline. The node does not assume that f is already multiplicative. This is the non-elementary comparison the assembly needs, not just additivity of a tangent space.

Step 3 uses precisely the regular-two-cocycle node's conclusion that a cocycle is db, applied over A_0 with its given coaction on E. That statement imposes no finite generation or flatness on E and does not require M to be torsion-free or D to be smooth. The second cited statement supplies the morphism tilde b and the sign c_(tilde b f)=c_f-db. Substitution makes the defect zero, and the same cited statement translates zero defect into equality of the two multiplication morphisms. Thus the use is from the statements, with the cochain sign checked against Conrad's displayed computation.

Step 4 is elementary cancellation in groups on universal affine points. Multiplicativity forces the identity value to be idempotent, hence the identity; evaluating on h and h inverse then gives the inverse diagram. It therefore proves all three operations preserved, as demanded in the item, rather than leaving the identity or inverse clause implicit.

For the edge cases I checked J=0 (zero coefficient module and no correction), the zero ring A (empty affine base), M=0 (trivial source; the unnormalized cochain formulation still corrects an arbitrary initial identity value), E=0 (only the zero cocycle), G trivial, and M=Z/p over characteristic p (a nonsmooth diagonalizable source). The arguments do not use reducedness or point detection by geometric points. Torsion in M only changes its indexing set and multiplication law; A[M] remains free. In the regular-cochain lemma R may be nonreduced and E nonflat, since the coaction formulation is the quasi-coherent coefficient category used by Remark B.2.4. I corrected the tempting overgeneral kernel-on-all-test-algebras formulation before writing the final node.

Both new nodes are statement-only, with no proof sketches, no proof dependencies and no hidden reference to the setting of another node. Their notions have inline definitions or cited definitions. Blueprint references retain the inherited route and fill exact source places; same_as is empty after the searches above. The item has four short steps, all under 2000 characters, and proof_deps is exactly their cited union. The citations file uses verbatim parts of each cited statement. This checks delivery-errors B through E substantively: no duplicate, elementary-only new node, restatement of the item, source-only proof step, unsupported citation, changed statement, or hidden field hypothesis remains.

## Unfinished work

No part of this one-level split remains unfinished. The two new nodes intentionally remain unsplit for subsequent stage-1 work. The requested local Conrad archive is still absent; its online text was available and read.

## Dry-run repairs

The first dry run rejected a citation excerpt shorter than 40 characters. Expanded that excerpt to include the full coboundary existence formula, and expanded the defect excerpt to its complete cocycle equation. No mathematical statement or proof changed.
