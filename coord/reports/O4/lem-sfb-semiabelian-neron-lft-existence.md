# Stage-1 delivery: lem-sfb-semiabelian-neron-lft-existence

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-semiabelian-neron-lft-existence.json: split item, statement unchanged, six proof steps with 17 statement citations.
- dag/nodes/sec-six-functors-basics/lem-sfb-abelian-neron-model.json: statement; no Mathlib match; abelian varieties over arbitrary Dedekind domains have finite-type Néron models.
- dag/nodes/sec-six-functors-basics/lem-sfb-split-torus-extension-neron-lft.json: statement; no Mathlib match; a character-free quotient with a Néron lft-model allows a split-torus extension to have one.
- dag/nodes/sec-six-functors-basics/lem-sfb-finite-flat-neron-lft-descent.json: statement; no Mathlib match; finite-flat descent and smooth closed subgroups for Néron lft-model existence.
- citations.json records a verbatim statement for every citation; searches.jsonl is the unmodified msearch log. The sandbox helper write_split.py generates only these owned node files and citations.

## Attachments

None. I searched the live read-only lean/WeilConjectures tree for the item tag, Neron, Néron and semiabelian spellings. There is no project declaration stating this item. In particular elliptic-curve reduction declarations returned by Mathlib searches do not construct a Néron model or assert its universal mapping property.

## WANTED

WANTED: Bosch–Lütkebohmert–Raynaud, Néron Models (1990), local PDF literature/bosch-lutkebohmert-raynaud-neron-models.pdf, 1.3 Corollary 2 (printed p.16), 1.4 Theorem 3 (p.19), 10.1 Definition 1 and Propositions 4 and 7 (pp.289–293), 10.2 Theorem 2 (pp.297–298), for the item and all three new nodes. The source path in the live item is absent. I read the primary-source scan at https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf online, including the theorem statements and proofs of Propositions 4 and 7. Printed p.289 is zero-based PDF page 295; printed p.297 is PDF page 303. The inherited source's page numbers 296/304 use one-based PDF numbering. No repository literature files were written or downloaded. The assembly is explicitly marked agent-written, as the brief requires when the local document is missing.

## What was wrong or incomplete

The item had no proof. Its statement is correct: the general existence criterion uses the fraction field of the strict henselization of the completion, not merely the original field when excellence is unavailable. I do not replace this with the false inference that arbitrary DVR completions are regular. For the semiabelian specialization I expose the construction actually used in the proof of the criterion: split the torus over a finite separable field extension, construct the abelian quotient's Néron model, use BLR 10.1/7, and descend by BLR 10.1/4. No imported statement was changed, and there is no statement dispute.

The blueprint ancestor is null in the live node, and tools/blueprint_refs.py ancestor reports None. This inherited null and the existing via chain are retained; new nodes have the item prepended to that chain and precise source places. Whole-blueprint searches for Néron, Neron, semiabelian, semi-abelian, split torus, torus extension, finite flat extension and primitive line found no corresponding theorem. I also read the current latest sk-thm-sf-ctf-stability unit, the stored unit and the chapter. This is a local ambient-model prerequisite inside the inherited trait-extension branch, not a replacement for any unit step.

## Not duplicates

No new node has a Stacks tag in its source, so there are no same-tag pairs requiring disambiguation. I searched the full DAG for Néron models, the BLR places and the relevant concepts before naming the three nodes. The only Néron-existence item is the owned node. The trait-hom-extension nodes prove extension between supplied models, not model existence. The new statements are general prerequisites, not the item's clauses: the abelian theorem has arbitrary Dedekind base and finite-type conclusion, the split-torus theorem assumes an already modelled character-free quotient, and the descent theorem assumes a model after a finite flat extension and handles smooth closed subgroups. None alone proves the item.

Existing lem-sfb-geometric-semiabelian-split-quotient supplies the finite Galois split quotient and is reused. Existing torus–abelian hom-vanishing, normalization finiteness, Dedekind normalization and DVR finite-freeness are reused. I did not create elementary nodes for connectedness under an open surjection, identifying the normalization's fraction field, or checking the group diagrams by universal-property uniqueness.

## Review by O4

I read BLR 10.2 Theorem 2 and its proof through 10.1 Propositions 4 and 7 rather than treating the theorem's semiabelian special case as another node. I read the new abelian-model statement against BLR 1.3/2 and 1.4/3: a global Dedekind model is of finite type; the base has no completeness, excellence or perfect-residue-field restriction. I read the split-torus statement against BLR 10.1/7: G must be smooth and connected, the torus must be split, the quotient must have no characters, and a model of that quotient is an input. Geometric connectedness and commutativity in my statement restrict the source theorem harmlessly. I read the descent statement against BLR 10.1/4, including the construction by Weil restriction, schematic closure and group smoothening: it asserts existence of a model of a smooth closed subgroup, not that base change of the final model equals the given model. The identity subgroup is permitted. All three new nodes carry only statements, empty proof lists and empty proof dependencies. Their deferred proofs remain future stage-1 items.

For step 1 I opened def-sfb-semiabelian-geometric-fibres and checked that it supplies the exact fppf split-torus/abelian sequence over every algebraically closed extension, including rank zero. I opened the smooth-affine-group torsor representability node: it asserts smoothness, surjectivity and universal openness of the actual represented torsor, not merely a definition of torsor. The torsor identification here follows directly by subtracting two lifts with the same quotient. Geometric torus fibres are connected. An open surjection with connected fibres over connected A is connected, by the clopen-partition argument written in the step. I opened the field-extension geometric-connectedness criterion and the geometric-semiabelian split-quotient node; the latter really gives a finite Galois extension, an abelian variety, a smooth surjection and the split-torus kernel. It does not require a perfect ground field. The item supplies every geometric hypothesis.

For step 2 I read each of the five cited statements: PID implies Noetherian and normal; a DVR has dimension one; separable finite extension gives module-finite normalization (Stacks 032L, algebra-lemma-Noetherian-normal-domain-finite-separable-extension); one-dimensional normalization is Dedekind and surjective on spectra (09IG, algebra-lemma-integral-closure-Dedekind); finite torsion-free DVR modules are finite free. I read the two Stacks source proofs in algebra.tex as well. The separability hypothesis is obtained from step 1, so no Nagata or excellence hypothesis is hidden. The denominator-scaling argument establishes Frac(C)=L explicitly. C is torsion free because it embeds in L. A nonzero finite free module is faithfully flat by its basis description, so the base extension used for descent is actually finite faithfully flat.

Step 3 cites exactly the abelian-existence statement and applies it over the Dedekind domain C to B/L. It uses the resulting universal property, not anything inside the proof of that prerequisite.

For step 4 I read the entire statement of lem-sfb-torus-abelian-hom-vanishing: it is only over an algebraically closed field. I therefore apply it to B over an algebraic closure, with rank-one target torus, and descend equality of morphisms using the actual equalizer statement of lem-a1-algebraic-space-fpqc-sheaf. A scheme is an algebraic space, and the affine faithfully flat field-extension cover is fpqc. Only after this check do I apply split-torus model existence to P_L with its character-free abelian quotient and the model from step 3.

Step 5 reads off finite-flat Néron descent with H=G=P and the identity immersion. R and C are Dedekind, and step 2 supplied finite faithful flatness. The output gives all smooth separated commutative model and universal-property clauses. Neither this step nor the statement claims finite type for N; split tori generally require infinitely many components.

For step 6 I initially considered a stack smoothness theorem over a field, then caught its base-field restriction during C4 review and replaced that citation before delivery. The final citations are the smooth-flat lemma, the scheme theorem for smoothness after flat base change (applied with both maps X→T), and scheme smooth composition. They apply to arbitrary DVR base. Thus X×_T X really is a permitted smooth test scheme. The equality of multiplication maps, identity maps and inverse maps follows separately from injectivity of the mapping bijections on X×_T X, T and X. It is an elementary uniqueness argument, not a new theorem node.

I checked delivery-errors B–E point by point. New statements introduce every object, define Dedekind domains and Néron models inline, cite the actual scheme and morphism definitions, and contain no proof sketches. TeX uses single mathematical backslashes after JSON decoding. Every proof use has a verbatim citation entry, proof_deps is exactly their union, and no proof uses a cited node's proof or creates a cycle through the item. Generic off-unit tools are declared in split_report.tool_uses. No SGA source is cited. No non-elementary step exceeds 2000 characters. I tested rank zero (abelian case), zero-dimensional identity group, positive-rank split tori (only lft, not finite type), nontrivial ramified Galois splitting extensions, imperfect residue fields and nonexcellent DVRs. The proof does not assume a supplied torus model or semiabelian reduction. No Lean was written, and no compiler or build tool was run.

## Unfinished

No unfinished part of this one-level split. The three statement-only prerequisites are intentionally unsplit. Required server dry-run and push results are recorded after validation below.

## Validation

The required deliver.py --no-push exited successfully: OK (not pushed), commit eded9947e52, preflight passed. Server preflight includes check_dag.py and review_split.py; they were not run locally. The earlier isolated server review_split call also passed. All three new nodes have the required logged searches; there are zero Mathlib leaves. The subsequent direct delivery runs the same preflight before pushing.
