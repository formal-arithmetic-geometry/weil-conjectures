# Q86 stage-1 delivery: lem-sfb-smooth-group-congruence-flat-scalar-extension

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-smooth-group-congruence-flat-scalar-extension.json: existing statement, now split into five proof steps. Not a Mathlib leaf. No new nodes and no new Mathlib leaves.
- citations.json: one literal statement quotation for each node used in each step (13 entries).
- report.md: this report. searches.jsonl is the search command's own log.

## Attachments

None. Searches in lean/WeilConjectures for the exact blueprint tag and for congruence, square-zero kernel and Lie terminology found no declaration stating the whole item. The existing infinitesimal-point and dual-number Lie declarations do not give this theorem for arbitrary A and J. No Lean was written, no compiler or Lake command was run, and the shared repository was only read.

## Wanted literature

WANTED: Brian Conrad, Reductive Group Schemes, Corollary B.2.6, proof, printed p.287, for lem-sfb-smooth-group-congruence-flat-scalar-extension; literature/conrad-reductive-group-schemes.pdf is absent locally. I read https://math.stanford.edu/~conrad/papers/luminysga3smf.pdf online, especially printed p.287 (PDF page 286), the paragraph identifying the kernel with the quasi-coherent Lie module and conjugation with the adjoint action. I did not download or write literature. The proof_origin is agent: the coordinate calculation makes this supporting assertion explicit using the local Stacks sources below. No SGA source is used.

## Corrections and scope

The statement is unchanged. The imported item had no proof, no proof dependencies and no proof origin. Its original Mathlib search records have been retained; five actual Q86 searches from searches.jsonl are appended with the exact query strings and returned result summaries. LeanFinder was tried in two phrasings, together with Loogle, LeanSearch and a Mathlib-source grep. The hits include derivationToSquareZeroEquivLift and extension/cotangent machinery, not this full group-scheme result. I read Mathlib/RingTheory/Derivation/ToSquareZero.lean:44-128 to check what the close hits actually state. The ingredients about finitely presented differentials and flat base change of Hom already have Mathlib-leaf nodes, and are cited rather than recreated.

The chapter, unit, latest blueprint unit text and inherited blueprint.from.place were read. The ancestor tool returns None for this inherited chain; I retained that existing ancestry record. Searches with blueprint_refs.py for congruence, square-zero, differentials finitely presented, and Hom flat, plus DAG statement/title searches, give no alternative blueprint statement of the item. The work supports the already recorded split-torus infinitesimal-conjugacy input to the alteration/moduli route; it changes no route or unit record. The generic lfp affine criterion is identified as a tool in split_report; it is itself an existing Mathlib leaf.

## Not duplicates

No new node was created. In particular I reuse lem-sfb-ring-finite-presentation-differentials (00RY), lem-weil-pbc-flat-base-change-hom-finitely-presented (087R), lem-weil-pbc-lfp-affine-opens-finite-presentation (01TQ), lem-weil-pbc-tensor-right-exact (00DF), lem-sfb-group-space-square-zero-kernel-module and lem-sfb-space-square-zero-lift-linearization (0618/04D0).

## Review by Q86

I read the worker brief, stage-1 rules, the three blueprint levels in SETUP.md, GOAL.md, and sections B through E of both copies of delivery-errors.md. I checked the item against Conrad's p.287 paragraph, and read the actual local Stacks statements and proofs of algebra.tex lemma-differentials-finitely-presented (00RY), lemma-tensor-product-exact (00DF), morphisms.tex lemma-locally-finite-presentation-characterize (01TQ), more-algebra.tex lemma-pseudo-coherence-and-base-change-ext (087R), and spaces-more-morphisms.tex lemma-difference-derivation and lemma-action-by-derivations (0618/04D0). There are no new nodes whose sources require separate review.

For step 1 I opened all four cited node files. The affine-spectrum node supplies the contravariant ring-map interpretation and the identity augmentation C→A. The lfp affine criterion really applies to all affine opens, hence to all of G and Spec A; I did not infer a global presentation merely from the local definition. The differentials node gives finite presentation over C without Noetherian hypotheses. The tensor exactness node gives the cokernel presentation after tensoring with A along the augmentation, without requiring A to be flat over C. Thus P is finitely presented over A.

For step 2 I opened both existing square-zero nodes and the differential and tensor definition nodes. The kernel-module statement supplies the original group law as addition and its canonical module structure. The linearization statement explicitly says the coordinate derivation is the difference of the two ring maps and gives its inverse. I wrote that difference on C and the inverse ε_B+D, verified the Leibniz identity with the quadratic term zero, and applied exactly the universal properties stated in the two definition nodes. The target ideal is JB and its square is zero for every B; it is not mistakenly identified with J tensor B at this point. The affine coordinate formula is the cited sheaf difference derivation, so the scalar action is the specified canonical one, not a newly chosen action.

For step 3 I opened the Hom base-change node and checked that its source can be any finitely presented A-module P and its target any A-module J: it does not assume J finite or A Noetherian. It is invoked only for A→B flat. The injection J tensor B→B follows immediately from the explicit exactness definition of flatness in the item's statement; its image is JB by the formula on pure tensors. I gave both directions of the tensor adjunction and the actual formula for the composite. This rules out silently applying flatness of B→B', or a finite-projective hypothesis not present in the chosen node.

For step 4 the only citation is the tensor-product definition: its statement explicitly says pure tensors generate. Everything else is the displayed difference formula of the preceding steps. Applying φ to k(c)−ε(c) proves coefficientwise naturality for every A-algebra map, without assuming φ flat. The identity at A uses the same coordinate formula. I checked that the argument identifies the map E_B specified in the statement, rather than only producing an unspecified linear isomorphism.

For step 5 I reopened the linearization statement: it says postcomposition by any morphism fixing the chosen base section is linear on difference derivations, with base ring Gamma(T0,O). Here the morphism is conjugation on G_B, so the scalar ring is B/JB. Its inverse is conjugation by g inverse. The group identities in the hypothesis give these morphisms and identities over Spec B; I do not invoke the field-only parts of def-sc-group-scheme. Identifying a map to G_B with its map to G together with the fixed structure map shows the canonical kernel module is the same one as in step 2. The last formula verifies naturality directly by multiplication and inversion. No flatness is used in this step.

I tested J=0 (all kernels and tensor modules vanish), the zero base ring, the trivial group, G_a (K_B=JB), and G_m (K_B=1+JB). The maps reduce respectively to multiplication J tensor B→JB and the identity differential formula. For a noncommutative example, GL_n gives matrices with entries in JB and conjugation by an arbitrary invertible matrix, which is B-linear. For a nonflat map between flat A-algebras one can take A=k[ε]/ε², B=A[t], B'=A with t→0: the formula still commutes. Infinite-dimensional square-zero J is allowed; neither the ideal tensor step nor the Hom theorem adds finite generation. Every proof step is below 2000 characters, and none hides a comparison or a standard lemma requiring a new node. B1–B10 are met by reusing existing statements; C1/C4 are checked as above; there is no clause relabelled as a new node, circular dependency or change of the target statement. citations.json records actual literal statements, not quotations bent to fit the proof.

## Unfinished work

None in this stage-1 split. Downstream unsplit dependencies remain their existing items. Required remote dry-run and delivery results are recorded below after completion.

## Delivery validation log

First required deliver.py --no-push invocation exited 1 without check diagnostics: srvpreflight's SSH subprocess timed out after 720 seconds, and its automatic nocheckout fallback then timed out after 600 seconds. No launcher script was changed, and no checker was manually run locally. The original invocation exited before retrying.
