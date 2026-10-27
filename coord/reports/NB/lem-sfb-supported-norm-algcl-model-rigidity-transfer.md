# Stage-1 report: lem-sfb-supported-norm-algcl-model-rigidity-transfer

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-supported-norm-algcl-model-rigidity-transfer.json`: existing statement, unchanged; six-step split.
- `dag/nodes/sec-six-functors-basics/lem-sfb-norm-local-model-finite-field-derived-generation.json`: new statement-only structural generation lemma; not in Mathlib.
- `dag/nodes/sec-six-functors-basics/lem-sfb-supported-coefficient-topology-defect-rigidity.json`: new statement-only relative coefficient-topology-defect lemma; not in Mathlib.
- `citations.json`: one verbatim statement quotation per citation per item step.
- `report.md`: this report. Search output is retained in `searches.jsonl`; local PDF text and scratch scripts stay in this item sandbox and are not delivery files.

## Attachments

None. I searched the live read-only `lean/WeilConjectures/` for the exact blueprint tag and the notions norm-topology, supported rigidity, coefficient defect and finite-field descent. No project declaration states this item. Existing sorry declarations are not attachments. No Lean file was written or compiled.

## WANTED

WANTED: an exact reference for finite-field derived generation of supported locally finite free modules over the **all-continuous, norm-topological** algebraic closure on an arbitrary qcqs scheme, with products and the specified uniformly bounded-below filtered diagrams; for lem-sfb-norm-local-model-finite-field-derived-generation.

WANTED: an exact reference for torsion-rigid closed-pair invariance of the actual two-term coefficient-topology defect of a supported finite-field local system, without a quasi-compact complement condition on the pair; for lem-sfb-supported-coefficient-topology-defect-rigidity.

These two assertions are outstanding mathematical obligations, not results quoted from HRS or Stacks. They remain unsplit, with no proof, proof dependencies or proof sketch in their statements. The item's assembly is agent-written. The source field identifies the exact blueprint place they serve and says that the full-generality reference is wanted.

## What was wrong or missing

The imported item was a statement-only conditional theorem without an argument. The live parent uses its full all-continuous conclusion. I have kept that statement, including the torsion-pair premise, every finite-field comparison premise, arbitrary support chains, and the uncompleted ambient categories.

Hemo–Richarz–Scholbach Lemma 7.9 cannot supply this implication: immediately before it the paper specifies the **colimit topology** on the algebraic closure. The existing `lem-sfb-lisse-finite-coefficient-model`, `lem-sfb-qcqs-lisse-stratified-integral-lattices` and coefficient-colimit nodes use finite-subextension-valued coefficients. Other norm-topology comparison nodes require separated finite-type schemes in positive characteristic prime to ell. Applying those to this pair would add missing hypotheses or change coefficients. None is used that way.

The historical unit record is the smooth-purity compactification-coherence unit. The item's actual ancestor and the newest blueprint place are in six-functors basics: the refinement-isomorphism paragraph of `det-sf-comp-coherence-cocycle`, through refinement (2), first paragraph. I read both newest proof files and the chapter/unit records. The split only expands the existing descendant closed-fibre coefficient comparison; it changes no chapter or unit route.

I considered finite-tree leaf descent as a provisional structural input but discarded it before delivery: a profinite family may vary through unbounded finite coefficient fields, so the hypotheses do not justify one finite field or finite stratification. The final generation node supplies neither. The earlier searches remain honestly recorded in `searches.jsonl`; they are not misattributed to the different generation statement.

An initial remote `review_split` identified a nonexistent mapping-cone citation. I replaced it by `def-weil-abstract-derived-category`, whose actual statement includes the cone formula and distinguished cone triangles. The next remote review passed. No tool or launcher file was changed.

## What remains unfinished

The two new lemmas are not proved in this stage-1 delivery. They split two independent issues: generation of arbitrary norm-coefficient local systems, which has no pair or cohomology assumption, and relative rigidity of a precisely defined coefficient-topology defect for finite-field-defined local systems, which has no finite-field comparison assumption. Neither alone implies the item: the former says nothing about restriction; the latter controls neither the finite-subextension term nor arbitrary norm-coefficient models. The assembly proves both of those missing links using the item's finite-field premise and the existing continuity theorem.

## Not duplicates

lem-sfb-norm-local-model-finite-field-derived-generation vs lem-sfb-supported-image-bounded-derived-generation: the existing node starts with all supported finite scalar B-local models and generates images of their maps; the new node starts only with B-extensions of finite-field local systems and generates the original supported B-local models. Applying the existing node cannot replace this assertion.

lem-sfb-norm-local-model-finite-field-derived-generation vs lem-sfb-finite-stage-supported-generation: the existing node concerns finite triangulated generation in the finite-subextension-valued category over separated finite-type schemes in characteristic different from ell; the new node concerns a larger explicitly defined closure in the full norm-continuous coefficient category over arbitrary qcqs schemes.

lem-sfb-norm-local-model-finite-field-derived-generation vs lem-sfb-continuous-algcl-stratified-finite-models: the existing node assumes separated finite-type schemes in positive characteristic prime to ell and supplies finite stratified field models; the new node has arbitrary qcqs schemes and a derived-generation conclusion, with no finite stratification or model assertion.

lem-sfb-norm-local-model-finite-field-derived-generation vs lem-sfb-continuous-qbar-constructible-generators: that node has a Noetherian hypothesis and already allows arbitrary norm-coefficient lisse generators; the new lemma must start with finite-field-defined generators.

lem-sfb-supported-coefficient-topology-defect-rigidity vs lem-sfb-supported-finite-stage-topology-defect: the existing node asserts Hom-orthogonality to a derived scalar unit cone on a separated finite-type scheme; the new node defines an ordinary two-term scalar-inclusion cone and asserts relative derived restriction on a torsion-rigid qcqs closed pair.

lem-sfb-supported-coefficient-topology-defect-rigidity vs lem-sfb-norm-algcl-cohomology-topology-comparison: the existing node asserts absolute global cohomology comparison on separated finite-type schemes in characteristic prime to ell. The new node assumes a torsion-rigid closed pair, does not assert that its defect is acyclic at either endpoint, and has no finite-type or characteristic hypothesis.

lem-sfb-supported-coefficient-topology-defect-rigidity vs lem-sfb-supported-norm-algcl-model-rigidity-transfer: the new node concerns a two-term defect for one finite-field-defined local system, without the premise B_E for any E. It gives no comparison for the finite-subextension endpoint and no reduction of arbitrary full-norm local models to these special ones. Steps 1, 3, 4 and 6 provide those separate arguments.

## Review by NB

I read the latest blueprint refinement proof (2), first paragraph, and the cocycle refinement-isomorphism paragraph, rather than an older snapshot. These give the compactification/direct-sum route but do not prove the new norm-coefficient assertions. I read HRS arXiv 2305.18131, Example 3.1, the open–closed formulas (3.3)–(3.4), Lemma 3.4, Proposition 4.3, Corollary 4.4, Lemma 5.3 and the paragraph before Lemma 7.9. In particular Lemma 7.9 is not a source for all norm-continuous coefficients. For the two new nodes I read these same source places and the existing related node statements above; the exact extension beyond them is expressly WANTED. I also read Stacks proetale.tex `lemma-ses-associated-to-open` (09AH) and derived.tex `lemma-third-isomorphism-triangle` (014A); they justify only the structural open–closed and triangle tools, not the missing analytic input. No SGA source is used.

Step 1 uses exactly the new generation node. Its root is the original qcqs T, its coefficient ring is the actual B, and its support-chain quantifier matches the item. It permits the covers and scalar modules of the original local model without a common field. Its generators use locally finite free finite-E sheaves, a special case of the finite scalar models in the hypothesis. This is not declared elementary.

Step 2 uses the internal/sectionwise transport statement, the exact inverse-image theorem for *any* condensed ring, the unit-normalized scalar section isomorphism, and K-injective comparison. I read each statement: transport preserves sections and the adjunction unit/counit, exact inverse image has no coefficient or complement restriction, scalar coherence explicitly has no flatness assumption and is invertible, and comparison into a K-injective target is unique in the homotopy category after precomposition by a quasi-isomorphism. The two resolution routes therefore compare the actual restriction maps. I do not use preservation of K-injectives by either scalar forgetting or t*.

Step 3 uses the actual tail-colimit statement with its specified inclusion maps, the scalar extension/restriction adjunctions, the module-forgetting colimit statement, ringed open–closed filtered continuity, open extension by zero, and internal transport. I checked that only C, the finite-subextension-valued coefficient, is expressed as a colimit. Every support-chain vertex is qcqs, inherited from its predecessor using finite affine covers for closed subschemes and quasi-compactness for open subschemes. Each closed chain arrow has quasi-compact open complement, exactly as required by the i_* filtered-colimit clause. A finite extension of the lisse E-model remains locally finite free, so every B_F premise applies. The underlying maps and their scalar actions are induced by the actual inclusions; no closure of an image is involved.

Step 4 uses the closed-restriction-derived-operations statement verbatim on a strict diagram of degree-zero E-module sheaves. Its common termwise lower bound is zero, the indexing category is the small directed tail from the cited coefficient-colimit node, and both schemes are qcqs. The cited statement supplies not merely object comparisons but compatibility with rho. Inverting all diagram arrows and taking their colimit gives an inverse of the restriction of H_C. There is no condition on the complement of t in that theorem.

Step 5 uses exactly the new defect node, the cone formula in the derived-category definition, the closed-restriction theorem's connecting-arrow compatibility, and the two-out-of-three triangle lemma. Its H_C and H_B are the E-module support extensions used in step 3, so D is exactly the complex in degrees -1 and 0 from the new node. No noncanonical choice of cohomology isomorphisms is substituted. The original torsion hypothesis verifies the defect premise; finite-field comparison was needed separately to control H_C. The first and third arrows of the morphism of cone triangles are isomorphisms, hence so is the middle one. Step 2 identifies this middle arrow with the full B-module generator restriction.

Step 6 uses the actual preservation and compatibility clauses of the closed-restriction theorem, and the triangle isomorphism lemma. I wrote out the inverse on a retract and both product/colimit inverse constructions, rather than concealing an extra generation or continuity claim. The class of invertible-rho objects meets all defining conditions of the new generated class. Thus minimality of that class applies to JL[0]. The final step is elementary relative to those cited structural statements; its content is explicit closure and the universal intersection, not another analytic assertion.

I tested small cases of both new statements. If X is empty or L is zero, the generation conclusion is the required zero object. If L is already the B-extension of a finite-E local system, with any support chain, it is a generator; this includes every trivial finite-rank model and the identity chain. On a geometric point, a local finite-free B-model is trivializable and is already among these scalar generators; profinite families with varying coefficient data are not forced into a finite stratification. The generation statement has no cohomological dimension or constructibility-preservation conclusion to contradict the known noncomplete coefficient Cech examples. For the defect, t=id gives an identity on the specified cone, N=0 gives zero, and empty source/empty root give zero. Since t* is exact, it carries the two-term complex to the same two-term construction on T0. The defect is allowed to have nonzero cohomology on either endpoint, so the known failure of absolute profinite Cech exactness for incomplete Omega is not suppressed. A claim that C=B, or that B has all the same absolute cohomology as C for arbitrary schemes, is nowhere made. These tests are checks of the proposed obligations, not proofs of them.

Against delivery-errors B–E: each new node is self-contained, statement-only and searched; every notion has an inline meaning or named definition; source places state the actual scope and the WANTED gap; no search is fabricated; every item citation is backed by the corresponding verbatim statement in citations.json. The duplicate comparisons above distinguish the nearby nodes. The original statement is unchanged, no derived object is replaced by a collection of per-degree statements, and every new proof step is below 2000 characters. The only preflight-independent open mathematical work is exactly the two new nodes, not an unmentioned inference in the assembly.

## Searches read

Searches were run only through the authorized msearch.py wrapper and are preserved with their actual responses in searches.jsonl. The two semantic phrasings for derived generation returned condensed free/solid constructors and generic sheaf-colimit facts, not the required generation. Loogle returned generic ObjectProperty.isoClosure declarations. The grep returned topological compact-generation documentation, which is a different assertion. The defect searches returned generic cochain resolutions, abstract quasi-isomorphisms, scalar-field normality or structure-sheaf restrictions, and generic presheaf cocones; none compares a closed pair with these coefficients. Earlier item and exploratory descent searches also remain in the log. No new node is a Mathlib leaf.
