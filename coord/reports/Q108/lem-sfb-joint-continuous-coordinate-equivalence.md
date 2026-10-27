## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-joint-continuous-coordinate-equivalence.json: statement, now split; no exact Mathlib match. Eight proof steps use the existing initial-topology Mathlib leaf and elementary calculations. The statement, statement dependencies, original citations/search records, creation metadata and blueprint provenance are retained.
- citations.json: one verbatim statement excerpt for every proof-step/node pair.
- searches.jsonl: genuine Q108 search-command records. No new DAG nodes and no new Mathlib leaves.

## Attachments

None. Searched the item tag and homogeneous/inhomogeneous coordinates in lean/WeilConjectures. Rep.homogeneousCochainEvaluation_bijective (HomogeneousCochainEvaluationBijective.lean:83) assumes compact Hausdorff G and discrete coefficients; Rep.exists_homogeneousCochains_inhomogeneous_coordinates (HomogeneousInhomogeneousContinuousCohomology.lean:55) also assumes total disconnectedness and gives additive equivalences for integer representations. They do not state this arbitrary topological E-vector-space assertion. The parent's lean/Sheaf/RepresentationTheory/TopologicalHomogeneousCochainCoordinates.lean existence theorem contains sorry at line 137, and its naturality theorem at line 184.

## Wanted sources

None. WANTED: none. The proof is explicitly agent-written, not attributed to a theorem of Stacks which does not occur there.

## Corrections and scope

The imported item had no proof. Its statement is correct and unchanged. The supplied Stacks 0DVG source defines continuous inhomogeneous cochains for arbitrary topological coefficients; it does not assert the homogeneous-coordinate equivalence. The proof_origin makes that distinction explicit. The existing initial-topology leaf supplies exactly the product continuity criterion; the algebra and the inverse substitutions are written out, without requiring an exponential law or locally constant coefficients.

The blueprint ancestor utility returns None for this created-item chain, although the parent's provenance identifies det-thm-sf-ctf-stability-direct-images. The item inherited blueprint.from.node=null; it is retained, along with its precise from.place and via. This metadata issue was already documented in the parent's independent review. I read the current main-20261015 direct-images statement and proof; the coefficient-comparison/transfer expansion is below clause (3), and this split does not change a unit route.

## Unfinished work

None within the stage-1 item. No Lean was written or compiled. The dry run and direct push are performed with the prescribed delivery tool.

## Not duplicates

No new nodes. The DAG/whole-blueprint searches for homogeneous coordinates and coordinate equivalence found the existing compact/discrete cochain nodes and the parent and siblings, not another statement of this unrestricted graded equivalence. The initial-topology criterion was reused rather than recreated. The differential/naturality siblings are not cited: no cycle through the parent is introduced.

## Review by Q108

I read Stacks etale-cohomology.tex, Tag 0DVG, section-continuous-group-cohomology, lines 9007–9040. Its arbitrary topological abelian coefficients support the coefficient scope; its displayed differential is outside this graded item's conclusion. I also read topology.tex, Tag 08ZS, section-limits, opening paragraph: product opens are unions of finite open rectangles. That verifies that product topology is the initial topology of the projections. I read the whole statements of lem-weil-pbc-initial-topology-continuity and def-weil-field, including the latter's blueprint_update. Every cited part is copied verbatim to citations.json. There are no new-node sources to review.

Step 1 uses the initial-topology node precisely for continuity iff every projection composite is continuous. Its objects are arbitrary spaces and maps, so the finite powers of J and the products E×V, V×V and J×V satisfy its hypotheses; the empty product causes no exception. Composition and constants are justified directly with inverse images. This is a generic Mathlib tool leaf, so no off-unit tool-use declaration is required.

Step 2 cites that same criterion to form the pairs of continuous functions before composing with the continuous addition/scalar maps assumed in the statement. It cites def-weil-field only for the ambient field notion, not for a theorem about continuous functions. Zero, addition, scalar closure, negation as multiplication by -1, and the pointwise vector axioms are checked directly. Equivariance closure uses exactly the assumed E-linearity of each action operator; it needs neither a norm nor finite dimension.

Step 3 cites the product criterion to pair each partial product with the next projection and to assemble P_n. The induction is explicit, with base 1 and step p_(i+1)=p_i*g_(i+1). The hypothesis used is joint continuity of multiplication in J. Precomposition with the given continuous F then proves continuity of Phi. Step 4 cites the same statement for the ratio tuple and the pair (x0,f(r_n(x))); the joint continuity assumption on the action, rather than mere continuity of its individual operators, is exactly what proves continuity of Psi. Inversion in J is continuous by hypothesis. All composition rules are the elementary inverse-image calculation already written in step 1.

Step 5 has no black-box citation: cancellation shows r_n(ax)=r_n(x), and the group action axiom gives equivariance. Linearity of Phi is evaluation; that of Psi follows pointwise from E-linearity of the action. Step 6 has no citation: p_(i-1)^(-1)*p_i=g_i proves Phi Psi=id, with n=0 explicitly checked. Step 7 has no citation: the induction starts at x0^(-1)*x0=1 and multiplies only adjacent inverse factors, preserving their order. Equivariance with a=x0^(-1) proves Psi Phi=id. Thus there is no assumption that J is commutative. Step 8 checks the degree-zero maps and assembles the already proved linear inverse identities, with no additional result.

I tested n=0, n=1 (Psi f(x0,x1)=x0 f(x0^(-1)x1)), the trivial group, V=0, non-abelian J, and characteristic two. The singleton convention identifies C^0 with V canonically and makes it a subspace of functions on J^0. No Hausdorff, compactness, discreteness, local compactness or completeness assumption entered a step. In particular the proof remains valid for non-Hausdorff topologies. For B–E of delivery-errors I checked: no new-node relabelling, no hidden independent lemma, every non-elementary input is the existing criterion with its exact statement, every other calculation is elementary and displayed, proof_deps is exactly the union of uses, no target statement or notion is weakened, no SGA is used, and every step is shorter than 2000 characters. Mathlib searches include LeanSearch, Loogle, two LeanFinder phrasings and grep; I read the relevant pinned Mathlib sources. Its iterated-continuous-map homogeneous complex and all-functions inhomogeneous complex are not the required joint-continuous spaces under these hypotheses. Prior unavailable searches remain honestly marked unavailable; current LeanSearch succeeded.
