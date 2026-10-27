# Worker report: det-lem-picard-affine

## Files written

- dag/nodes/sec-picard-framework/det-lem-picard-affine.json: statement, split; no Mathlib match. The proof applies the exact existing DAG node lem-pc-affine-vanishing. The statement is unchanged.
- citations.json: the full verbatim statement of lem-pc-affine-vanishing supporting step 1.
- searches.jsonl: six actual msearch.py searches, all available; two semantic phrasings, LeanSearch, Loogle and two source searches. No new node files; zero new Mathlib leaves.

## Attachments

None requested. The previous failed attachment is not repeated. I read AlgebraicGeometry.Scheme.Modules.subsingleton_H_succ_of_isAffine in lean/WeilConjectures/AlgebraicGeometry/Cohomology/Affine/Cech.lean:247, including its hypotheses, conclusion and proof. It is already recorded by the existing lem-pc-affine-vanishing, whose slopmaster2 audit says closed. The present delivery cites that DAG node, rather than submitting another attachment or introducing a node for the declaration.

## WANTED

None.

## Findings and corrections

The newest literature/blueprint/latest/blueprint/sec-picard-framework/sk-thm-picard-perfect/det-lem-picard-affine.md has precisely the item's statement and no proof. The item is a detail lemma, not its unit's key statement. I read dag/chapters/sec-picard-framework.json and dag/units/sk-thm-picard-perfect.json; neither is changed.

The inherited proof attempted to redo the standard-cover Cech argument, left its first step unjudged and without citations, and cited the broad section tag 01EO rather than a node stating the Cech vanishing criterion. The precise source results are coherent.tex Tag 01XB (lemma-quasi-coherent-affine-cohomology-zero), its standard-cover input in coherent.tex (lemma-cech-cohomology-quasi-coherent-trivial), and cohomology.tex Tag 01EW (lemma-cech-vanish-basis). These sources were read. The DAG already contains both the exact affine theorem and the criterion; reimplementing their proofs would duplicate existing work. I replaced the inherited proof with an application of the existing exact theorem and added the statement's missing notion dependencies. The imported flags and blueprint metadata remain intact. No statement dispute or source error was found.

## Not duplicates

No new nodes were created. A whole-DAG and blueprint search found lem-pc-affine-vanishing and sk-lem-picard-affine with exactly the same statement, and pqf-lem-affine-vanishing with the more general affine-open statement. The first two are recorded in blueprint.same_as. The proof cites lem-pc-affine-vanishing, so it does not move the item's content into a new node (D1/D2). Its existing proof dependencies are lem-pc-affine-cech-complex only; it does not depend on this item. The closed audit cuts the existing proof branch. The module-valued basis criterion lem-weil-pbc-module-cech-vanishing-basis was also opened and checked, but is unnecessary in this assembly. No off-unit tool declaration is needed for the already-closed cited node.

## Unfinished work

None in the split. Independent maintainer review remains the normal next step after delivery.

## Review by Q129

I compared the item's entire unchanged statement to the current blueprint detail and to coherent.tex Tag 01XB, label lemma-quasi-coherent-affine-cohomology-zero. The source says vanishing on any affine open of any scheme for a quasi-coherent module. Taking the whole affine scheme gives exactly the item, for all positive degrees. The proof in that source uses standard affine coverings and the ringed-space criterion 01EW; it does not require noetherianity, finite generation of the module, or a hypothesis on the characteristic. I also read the node lem-pc-affine-vanishing itself: it states the affine-scheme conclusion with precisely these hypotheses, and its Lean audit is closed. This is an existing theorem reuse, not a replacement of the unit's geometric proof route.

Step 1 uses only the statement of lem-pc-affine-vanishing. Its variables X, A and F are the same variables as the item; renaming its degree p to q gives the conclusion directly. citations.json quotes its whole statement, including both hypotheses and the quantifier over positive degrees. No construction from its proof is used. The step is marked non-elementary because it invokes the affine theorem; the assembly after invocation is just substitution. There is no hidden Cech comparison or restriction-cohomology identification in this application: the two natural-language statements use the same cohomology convention.

For the statement dependencies I opened def-pc-scheme (which includes affineness as an isomorphism with Spec of a commutative ring), def-weil-sheaf-of-modules-category, pqf-def-coherent (whose first clause defines quasi-coherence), and pqf-def-cohomology (which specifies derived global sections of modules). These supply the notions that were missing from stmt_deps. They are not cited as if they proved vanishing. I also checked the distinction between module-derived and underlying abelian cohomology recorded in the project: this split uses the existing natural-language module-cohomology theorem as stated and does not silently replace a coefficient category based on the spelling of the Lean declaration.

The small cases are consistent: A may be the zero ring (empty affine scheme), F may be zero or an arbitrary non-finitely-generated module sheaf, and q may be 1; each satisfies the cited theorem without an extra condition. Degree zero is excluded in both statements: for X = Spec k and F = O_X, H^0 = k need not vanish. No new statements require separate small-case testing. No proof step exceeds 2000 characters.

I checked B1-B10 against the delivered file: no new statement-only node, no new source or leaf record, no unrun search, and blueprint.same_as now names the exact existing duplicates. For C1-C8 the only theorem citation was opened and quoted, no proof-internal object is borrowed, and the existing dependency chain has no return edge to this item. For D1-D5 no argument was displaced into a new node and no omitted standard fact remains inside the assembly. For E1-E7 the direct variable substitution preserves all hypotheses and the object whose cohomology vanishes. The Mathlib hits were read: they concern quasi-coherence definitions, localizations of sections, generic derived cohomology, or empty-scheme ell-adic vanishing, not the theorem for a quasi-coherent module on an arbitrary affine scheme. Both semantic phrasings failed to produce an exact Mathlib match; the actual searches are recorded without inventing unavailable results.
