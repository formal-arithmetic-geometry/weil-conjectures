# Stage-1 report: lem-sfb-continuous-frame-sheaf-comparison

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-continuous-frame-sheaf-comparison.json — item, statement; split by eight explicit proof steps. No complete Mathlib match.
- citations.json — verbatim statement excerpts for every dependency cited in every proof step.
- report.md — this report and direct-delivery self-review.

No new nodes and no new Mathlib leaves. No unit record needs editing: this is a supporting node, not the unit's key statement. The statement, statement dependencies, blueprint ancestry, source, title and creation record remain unchanged. Existing search records are retained; six logged Q28 searches are appended.

## Attachments

None. I searched lean/WeilConjectures/ for the exact blueprint tag and the continuous-frame, continuous-lattice and lattice/tensor concepts. The project has continuous ring presheaves and sheafhood in WeilConjectures/CategoryTheory/RingObjects/ContinuousMap.lean (notably isSheaf_continuousMapRingPresheaf, line 97). This covers only the coefficient-ring part, not the frame isomorphisms, actual-inclusion scalar extension, inverse formula and restriction compatibility. It is not an attachment for this item.

## WANTED

None.

## Findings and changes

The repository item was unsplit; the sandbox contained only dispatcher markers, so I copied the live item and continued from its existing searches and statement. The precise source is main-20261015/sk-lem-stratified-lattice.proof.md, “Pushing down by the trace”, and the accompanying sk-lem-stratified-lattice-trace.proof.md, “Local computation”: the sum lattice is finite free, and its associated coefficient sheaf becomes the full ambient vector sheaf after extension of scalars. The extracted item makes this coordinate assertion for a general topological field and a specified homeomorphic integral frame. This generality is valid; no statement dispute or unit-route change was needed.

The terminology “constant lattice” means continuous functions into the lattice with its specified topology here. I did not substitute a constant discrete presheaf. The proof uses the existing Mathlib leaf lem-cbc-continuous-functions-fpqc-sheaf for actual sheafhood and writes out the remaining finite-coordinate calculations. In particular, it does not infer a sectionwise tensor formula from a sheaf tensor formula; it constructs the sectionwise inverse first and only then passes to sheafification.

## Mathlib and duplicate searches

Q28 ran LeanFinder twice, Loogle, LeanSearch and two grep searches through the required msearch.py command. I read their hits, and retained the precise query strings and actual outcomes from searches.jsonl. ContinuousMap.tensorHom (Topology/UniformSpace/ProdApproximation.lean:90–95) has tensor over the constant coefficient ring and target continuous functions on a product of spaces, rather than the map here. ContinuousMap.module' (Topology/ContinuousMap/Algebra.lean:826) supplies only the pointwise module structure. continuous_equivFun_basis (Topology/Algebra/Module/FiniteDimension.lean:296–298) and Module.Basis.constrL (line 434) require stronger normed-field/Hausdorff hypotheses; they do not state this item. SheafOfModules.free (Algebra/Category/ModuleCat/Sheaf/Free.lean:39) is an abstract coproduct construction and does not give these continuous-function or inclusion comparisons. None is an exact match or a one-line specialization of the whole item.

Before deciding the dependencies, I searched the whole DAG and blueprint for continuous frames, continuous functions, lattices and tensor comparisons (including blueprint_refs.py search and ancestor). The nearest ancestor is sk-lem-stratified-lattice, through lem-sfb-continuous-lattice-sum. No blueprint node states this coordinate comparison. Existing lattice/sheaf nodes were read, including lem-weil-pbc-constant-matrix-lattice-pair, lem-weil-pbc-lattice-free-scalar-extension and lem-sfb-finite-free-scalar-coordinates. No node was created.

## Not duplicates

No new-node pairs. The item is not identified with lem-weil-pbc-constant-matrix-lattice-pair, which asserts existence of an embedded sheaf pair; this item fixes an arbitrary topological submodule with a homeomorphic frame and gives sectionwise maps and their inverses. The abstract free-sheaf scalar-extension lemma gives no sectionwise continuous-function formula. lem-sfb-finite-free-scalar-coordinates assumes the coefficient algebra itself is finite free over the base ring, which is not assumed here.

## Review by Q28

I read the stage-1 brief, delivery-errors B–E, the three-level rule, GOAL.md, the chapter and unit records, and the two blueprint source proofs named above. The eight steps remain within the unit's trace-lattice computation. No source is SGA, and no Lean or build tool was run.

Step 1 checks continuity using the actual subspace topology on A and L. The two cited definitions specify continuous-function coefficients, precomposition, pointwise module structure and semilinear restrictions; their statements were opened. The restrictions of continuous ambient operations land in the subring/submodule, so the argument requires no closedness, completeness or norm. This is a finite-coordinate application of the definitions.

Step 2 is the non-elementary sheafhood step. I opened the entire statement and Mathlib match of lem-cbc-continuous-functions-fpqc-sheaf, and read ConstantSheaf.lean:102–119. It says exactly that continuous maps to any additive topological abelian group form an fpqc sheaf; it explicitly imposes no Hausdorff condition. Its hypotheses hold for A, K and L by step 1. The cited proétale-site definition explicitly says its covering families are fpqc covering families, and I checked this clause in the file. Thus the restriction of the gluing assertion to this small site is justified. The module-sheaf definition supplies exactly the semilinear-restriction criterion being checked. All three quotes are copied from the cited statements in citations.json.

Step 3 constructs the forward and inverse maps, rather than assuming a continuous basis theorem for topological modules. Their continuity follows from the assumed homeomorphism beta and coordinate projections. Both inverse equations and linearity are pointwise applications of the basis identities. The equations with precomposition establish naturality for every site arrow, not only for a chosen covering. No additional lemma is hidden here.

Step 4 checks the actual inclusion on sections and the identification C(|U|,K^r) = C(|U|,K)^r by coordinate maps. The K-basis hypothesis is used here to give the matrix inverse. Continuity of both matrices is checked directly as finite sums with fixed coefficients, so automatic continuity for arbitrary finite-dimensional topological vector spaces is not being invoked. Injectivity follows pointwise from the given subset L in K^r.

Step 5 constructs mu by the balancing relation and constructs its inverse psi with the exact formula requested. I checked both composites: B B^{-1} gives mu psi, while the A-valued coordinate expansion of f from step 3 and tensor balancing give psi mu on each elementary tensor. Finite sums of elementary tensors then give the identity on the tensor module. This calculation does not assume T is a field, R is a domain, or sections extend from a cover. In particular, it is valid on the empty scheme where these section rings are zero rings.

Step 6 separately proves the usual finite-coordinate tensor identification by an explicit inverse, then identifies mu with B on elementary tensors. Its two displayed restriction calculations use that the b_i and the entries of B^{-1} are constant. Thus neither the matrix comparison nor compatibility of the tensor inverse has been left as an assertion of transport.

Step 7 uses exactly the definitions in def-pur-sheaf-tensor-product and def-weil-pbc-sheafification, whose full statements I opened. I also read Stacks sites-modules.tex, section-tensor-product (03EK), lines 3550–3579, and sites.tex, proposition-sheafification-adjoint (00WH), lines 2052–2059. The first says that the sheaf tensor is the associated sheaf of the sectionwise tensor, and the second gives the factorization/uniqueness property. The proof explicitly derives that the sheafification unit of an already-sheaf presheaf is invertible, using that uniqueness twice. This is a short consequence of the cited definitions, not an uncited comparison theorem. It also identifies the sheafified morphism with the scalar extension of the actual inclusion by its elementary-tensor formula.

Step 8 verifies the empty-index case rather than removing it: L is zero, all sums are empty, the unique 0-by-0 matrix is invertible and tensoring the zero module gives zero by the tensor relations. Further small cases checked were rank one L=cA for c nonzero (mu is multiplication by c and psi uses c^{-1}), L=A^r (B=1), A=K, empty test schemes, and an indiscrete field topology. In each case the explicit inverse formulas work. No compactness or separation assumption appears in their proof. There are no new statements needing a separate edge-case audit.

For B1–B10, there are no new unsplit statements, no duplicate or clause-renaming nodes, no new missing notion, and all existing item fields outside the split-owned fields are preserved. For C1–C8, the sole substantial imported sheafhood fact is cited exactly; all other algebra is expanded in the steps, every cited statement was opened, and citations.json has a verbatim quote for each step/use pair. proof_deps is precisely the union of the uses. The definitions and Mathlib leaves used from other units are permitted generic tools; no off-route statement tool is needed. For D1–D5, the proof carries its coordinate argument directly and neither delegates the item's clauses to fresh nodes nor relies on details in another node's proof. For E1–E7, the actual topologies, both basis hypotheses, arbitrary scheme, restriction maps, zero rings and rank-zero case were checked as described. No source correction was needed. Every proof step is shorter than 2000 characters; no long step hides a separate lemma.

## Unfinished work

No mathematical part is left unfinished. The required server dry run and direct delivery follow this review.
