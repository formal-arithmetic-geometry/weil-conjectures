# Stage-1 report: lem-sfb-homogeneous-coherent-acyclicity

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-homogeneous-coherent-acyclicity.json: statement item, split into four proof steps using existing nodes. Mathlib verdict: no match after recorded LeanFinder, LeanSearch, Loogle and grep searches, including a second semantic phrasing.
- citations.json: one verbatim quotation for each node cited by each step.
- report.md; searches.jsonl is the unmodified search-command log. write_split.py is sandbox-only preparation code.

No new nodes; no Mathlib leaves. No unit record is modified: this supporting lemma is not the unit's key statement.

## Attachments

None. I searched lean/WeilConjectures by the exact blueprint id and by translation invariance, homogeneous line/invertible modules, and Picard acyclicity. The source matches were unrelated graded-module and Artin–Schreier translation results. The item has no Lean declaration to attach. Its inherited search records are preserved and this worker's actual reruns are appended, including the current ring-Picard hits absent from the previous summary.

## WANTED

None. The Milne PDF and the Stacks sources needed for every supporting input are available locally and were read. The acyclicity proof itself is agent-supplied, as the original item's source explicitly says, rather than attributed to an unprinted theorem of Milne.

## What was wrong or missing

The imported supporting item had a correct statement but no proof. The exact statement, all hypotheses, and its characteristic/dimension scope are preserved. In particular algebraic triviality is not assumed or derived via a circular use of the parent lemma.

The nearest-blueprint helper prints `blueprint.from.node = None`: the inherited created.item chain ends in the Lean-module identifier Sheaf.SixFunctors.CtfStabilityDirectImages rather than a DAG node. I retained the existing blueprint field, including its precise from.place and via list. The chain's oldest DAG node lem-sfb-admissible-direct-image points to det-thm-sf-ctf-stability-direct-images. I read that node's current latest blueprint statement and separate proof, as well as the unit and chapter records. This is a lower-level tool for the inherited Milne polarization prerequisite, not a change to the direct-image route. No claim is made that the current blueprint itself prints this coherent-cohomology argument.

## What could not be finished

Nothing in the stage-1 split remains unwritten. Supporting nodes retain their existing individual stages; this delivery does not claim to formalize the proof in Lean.

## Not duplicates

No new nodes are created. DAG searches found existing interfaces for every non-elementary input. In particular the already-existing rigidified-product-seesaw is used directly instead of introducing another homogeneous-to-multiplicative lemma; flat-base-change-cohom, the invertible-factor projection formula, and proper coherent finiteness are reused. A whole-blueprint search for homogeneous coherent acyclicity returned zero matches; a broader homogeneous search was also read. The relative algebraically-trivial multiplicativity node is deliberately unnecessary: its hypothesis would have required the parent assertion we are supporting.

## Review by Q54

I read Milne, Abelian Varieties, I Proposition 8.4(b),(c), printed pp.35–36 (PDF pp.41–42), and Theorem 5.16/Corollaries 5.17–5.18, printed p.26 (PDF p.32). I also read Stacks coherent.tex, lemma-flat-base-change-cohomology (02KH), proposition-proper-pushforward-coherent (02O5), lemma-proper-over-affine-cohomology-finite (02O6); cohomology.tex, lemma-projection-formula (01E8), including its resolution proof; and varieties.tex, lemma-proper-geometrically-reduced-global-sections (0BUG), including the constants clauses and proof. No new-node source needs review because there are no new nodes. The proof_origin records the distinction between the printed multiplicativity argument and the agent assembly for acyclicity.

For Step 1 I opened def-sc-abelian-variety and checked that properness, smoothness and connectedness are actually in its statement. I read lem-sc-abelian-variety-characterization and took only its explicit geometric-integrality conclusion. I checked that lem-pc-h0-proper-variety(2) gives constants for precisely a proper geometrically integral scheme. The identity is a rational point, so the empty scheme cannot occur.

For Step 2 I checked the statements of def-pc-module-pullback, def-sc-invertible-module, and lem-pc-tensor-dual-invertible: they supply tensor pullbacks, local rank-one frames, and actual dual-pair evaluation isomorphisms. I opened lem-sfb-rigidified-product-seesaw and used its explicit final conclusion H = q^*s_x^*H, not anything from its proof. Its source is the Milne seesaw just read. Its V must be proper geometrically integral, which Step 1 proves; its parameter T must be smooth separated and finite type, all satisfied by A. I explicitly computed both the fibre restriction and identity-axis restriction of N, including the constant one-dimensional factors P_y and P_e. Choosing frames of these factors is a field-vector-space operation, not an algebraic-triviality hypothesis. Thus multiplicativity is proved in the item rather than moved to a restatement node.

For Step 3 I read pqf-def-cohomology to fix ordinary Zariski module cohomology and higher direct images. I read lem-fin-proper-coherent-finite-dimensional and checked its two coefficient requirements: P is quasi-coherent and finitely presented because it is locally free of rank one. I read lem-pc-flat-field and the FULL statement of lem-pc-flat-base-change-cohom. In particular the latter gives a sheaf-valued higher-image isomorphism, not merely dimensions after a field extension; it applies to the base change of A -> Spec k by itself, with the base morphism flat and the original morphism qcqs. The properness in Step 1 supplies qcqs. I read lem-pc-projection-formula and used only its stated invertible-factor derived isomorphism. Passing to degree i is exact tensoring with a line module, verified in a local frame. I wrote the shear sigma, its inverse, and both identities over p_2 explicitly. Its cohomological comparison is a routine resolution argument: an isomorphism induces inverse exact equivalences of module categories, preserves injectives, and p_2 composed with either shear is p_2. This is not a hidden general base-change theorem. The resulting vector space is the same V on both sides, not H^i(A,O_A).

For Step 4 I verified the matrix calculation against local frames. The identity uses the (1,1) entry of u v on the trivial bundle and therefore gives a sum equal to 1 in k. Some summand is nonzero in any characteristic. That summand provides a section and a functional whose composite is an invertible constant. On a rank-one local frame the two composites agree by commutativity, so the section actually trivializes P. This is a few-line elementary argument from Step 1 and Step 3, not an additional lemma node. I avoided both taking a trace and dividing by n: these would cause a real issue when the characteristic divides n. Taking only determinants would show torsion and would be insufficient; the written matrix argument proves triviality.

I checked the B–E return categories against the final node: it is self-contained, no statement was weakened, every non-elementary input has a cited node whose actual statement supplies the input, proof_deps is exactly the union of uses, and all citation quotes are verbatim substrings checked against the live node statements. There is no new statement-only node to hide the item or one of its clauses. No source forbidden by the route lock is used. Generic off-unit tools are explained individually in split_report.tool_uses. I tested dimension zero (the nontriviality assumption is impossible), i=0 (the same higher-image calculation applies), P=O_A as an excluded boundary case (the contradiction step then no longer applies), and arbitrary positive characteristic, including characteristic dividing n. Each step has fewer than 2000 characters and is a single assembly argument; there is no concealed long-step lemma to extract.

## Dry-run repairs

The first dry run rejected a too-short quotation for geometric integrality (the selected words were verbatim but under 40 characters). I replaced it with the entire existing characterization statement; the proof citation itself was already correct.
