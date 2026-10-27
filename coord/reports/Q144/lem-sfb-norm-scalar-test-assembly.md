# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-norm-scalar-test-assembly.json`: statement unchanged; seven proof steps, status split. Mathlib search: no match.
- `citations.json`: verbatim statement quotations for every step citation.
- No new nodes and no Mathlib leaves. All intermediate facts already have nodes.

## Attachments

None. Searches of `lean/WeilConjectures/` for the blueprint tag, norm/completion cohomology, and continuous algebraic-closure coefficients found no declaration giving this statement. The constant-subsheaf completion and derived adic completion results concern different objects.

## WANTED

WANTED: an exact ordinary all-continuous norm-topological proof of `lem-sfb-norm-completion-positive-cohomology-mono`, including the noncomplete algebraic closure and punctured regular affine finite-locally-free limits. This is the existing open input, not a result claimed from HRS or from the blueprint. This assembly uses its stated injection and does not attempt to split that node.

## Problems found

No statement dispute. The source paragraph (3) gives the direct-image route but does not contain this expanded scalar comparison. I retained agent proof provenance and used the full argument preserved as original steps 6--7 in `coord/reports/Q67/lem-sfb-torsion-acyclic-norm-coefficient-test.md`. The item is not its unit's key node, so no unit record is changed. Its nearest blueprint ancestor is null, as printed by `blueprint_refs.py ancestor`; the existing null and via chain are preserved and the exact paragraph/step place is already filled.

The original argument omitted explicit justification of the coefficient norms being totally disconnected and of negative derived cohomology. The split writes the clopen-ball separation, quotient factorization and completion-limit arguments, and cites the existing negative-vanishing and bounded-below/unbounded comparison nodes. No step exceeds 2000 characters.

## Unfinished work

None for the one-level split. The positive completion injection is still the independently queued node identified above; this delivery makes no claim of a completed Lean proof.

## Searches and reuse

Before writing I searched the whole DAG for completion, clopens and component spaces, opened the matching statements, and ran `blueprint_refs.py search` for `completion`, `scalar restriction` and `continuous functions`. The returned blueprint nodes give coefficient definitions or special component computations rather than this assembly. The existing scalar-comparison and positive-completion nodes are reused. I ran logged LeanFinder searches in two phrasings, LeanSearch, Loogle, and Mathlib grep with the exact queries recorded in the item and in `searches.jsonl`. The hits give completion maps and normed fields, affine basic-open identities, Galois topology, and profinite locally constant functions, not this cohomological restriction. I read Mathlib's `NumberTheory/Padics/Complex.lean` and `Analysis/Normed/Module/Completion.lean` to distinguish the field infrastructure from a sheaf-cohomology theorem. No search was inferred or invented. Prior searches inherited from the live node remain intact.

## Not duplicates

No new nodes. In particular `lem-sfb-spectral-clopen-component-homeomorphism`, `lem-sfb-normed-field-completion`, and `lem-sfb-norm-completion-positive-cohomology-mono` are cited rather than restated as new nodes.

## Review by Q144

I read the current blueprint direct-images proof, paragraph (3), and the retained original steps 6--7 in Q67's report. The former provides only the open-coefficient/direct-image route. The latter supplies this agent-formulated norm argument; neither is used as an assertion that incomplete coefficients are automatically completed. I read Hemo--Richarz--Scholbach, Example 3.1, for the all-continuous-function realization, and Stacks `sites.tex` Tag 0H7J (`example-constant-sheaf`), `properties.tex` Tag 094L (`lemma-quasi-compact-quasi-separated-spectral`), and `topology.tex` Tag 0906 (`lemma-spectral-pi0`). The finite-extension norms and completion are existing Mathlib-backed nodes, not a new attribution to a missing local-fields source.

For step 1 I opened `lem-weil-pbc-proetale-finite-constant-representable`: it gives exactly the labelled-coproduct representation, including naturality in all finite label maps. Maps into this coproduct are clopen partitions; naturality gives the pointwise ring operations. Thus the actual degree-zero restriction is a ring map, and the elementary idempotent calculation turns its given bijection into the clopen inverse-image bijection. This uses the field property of Z/ell, including ell=2, rather than incorrectly using idempotents of an arbitrary finite ring.

For step 2 I opened the affine-qcqs, qcqs-spectral and spectral-clopen-component-homeomorphism statements. V is affine by hypothesis and T is its principal affine open, so both qcqs hypotheses hold. The topology lemma requires only continuity of the inclusion and the clopen inverse-image bijection, not a properness or surjectivity hypothesis. Its normalization identifies the actual induced component map, which is essential for step 4.

For step 3 I checked the absolute-value node: it states the ultrametric inequality for every finite extension with the extending norm, so it applies to E and to the finite extension generated by any chosen pair in Omega. The written clopen-ball argument establishes the total-disconnectedness required by `lem-weil-pbc-condensed-field-continuous-realization`. I read that statement: it applies to any scheme and a totally disconnected normed field, not just complete or finite fields. It identifies the ring sheaves canonically, so restriction is the actual continuous-function restriction. Step 4 is then a direct quotient-topology argument; its displayed inverse is continuous and its normalization checks that it is an inverse to restriction, without any finite-subextension factorization.

For step 5 I opened `lem-weil-pbc-proetale-abelian-evaluation-colimits`, whose hypothesis is exactly the item's epimorphism-surjectivity definition of weak contractibility. It states preservation of homology and therefore gives acyclicity of the evaluated K-injective resolution; no nonexact arbitrary evaluation functor is used. The same conclusion on the localized site follows by viewing its sheaves in the slice over the represented object: forgetting a sheaf epimorphism in that slice retains an epimorphism, and a lift of its section remains over V. `lem-weil-l-adic-extension-complete` states completeness for the same extending norm on E. Hence E is among the complete nonarchimedean fields quantified in the assumption, which proves the E restriction itself, not just an abstract comparison.

For step 6 I opened both the normed-field-completion and positive-completion-cohomology statements. The first gives a complete normed field and an isometric canonical inclusion; continuity passes the ultrametric inequality to the completion. This verifies every complete-test hypothesis, including the isometric Q_ell extension. The second gives only an injection for q>=1 and requires the regular affine finite-type system, finite locally free transitions, stagewise nonzerodivisors and affine weakly contractible V. These are all copied unchanged from the item. Its punctured test is exactly T=V[1/f_V]. The completed cohomology is zero by the assumed restriction test and source acyclicity, so injection suffices to prove vanishing for the original Omega coefficients. No surjectivity or equivalence under completion is asserted.

For step 7 I opened the generic ring-sheaf Grothendieck statement, the negative-vanishing statement, the bounded-below/unbounded comparison, and the derived-category definition. Integer-module sheaves are abelian sheaves on these small sites, so the hypotheses for the right-derived negative vanishing hold. Sections are left exact by sectionwise kernels. The comparison has the requisite injective and K-injective hypotheses in this Grothendieck setting, already used by the item's stipulated K-injective derived sections. The degree-zero identification is written directly from a nonnegative resolution. All cohomology maps are those of restriction, so the quasi-isomorphism inverted in D(Ab) is precisely the requested map.

I checked empty V (hence empty T), an empty T with nonempty V (ruled out by the cyclic section hypothesis), the identity open, ell=2, and arbitrary noncomplete Omega. Empty function sets consist of the unique zero section, the component homeomorphism proof chooses no points, and the resolution arguments give zero cohomology. I checked delivery-errors B--E: the statement is self-contained with its definition dependencies retained; every non-elementary input is a cited existing statement, not its proof; verbatim citations are recorded; there is no new-node relabelling or cycle through the parent. Generic tools from other units are declared in `split_report.tool_uses` for maintainer review. No Lean is written or compiled.
