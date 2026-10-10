# Delivery report: `lem-weil-pbc-fs-adic-local-flat`

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-fs-adic-local-flat.json`: split Stacks Tag 07NP into six proof steps.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-fs-adic-complete-source-target.json`: statement node for Tag 07ED, the completion of both source and target; no Mathlib match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-complete-local-flat-presentation.json`: statement node for Tag 07NN, the flat Cohen presentation; no Mathlib match.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-flat-module-retract.json`: Mathlib leaf, exact match `Module.Flat.of_retract` in `Mathlib/RingTheory/Flat/Basic.lean:172`.

## Attachments

None. The node has no Lean declaration in either audited source tree.

## WANTED

None. The pinned `literature/stacks-project/` payload was absent from this checkout, so I checked the canonical online Stacks pages for Tags 07NP, 07ED, 07NN, 07NJ, 0316, 0584, 00MC and 00HI. Their tags, labels, statements and proof route agree with the places already recorded in the DAG nodes.

## Corrections and proof route

The imported node had the correct statement and complete Mathlib searches but no proof. The split follows 07NP exactly: pass to the maximal-ideal completions using 07ED; descend flatness afterward using completion faithful flatness; in the complete case choose the 07NN square; identify `S/IS` with the flat base change `S tensor_R A`; apply 07NJ to the quotient `S/IS -> B`; and use that a module retract of a flat module is flat.

The 07NJ application is checked explicitly. Put `C = S/IS` and let `J` be the kernel of the surjective local map `q : C -> B`. Locality and surjectivity give `q(m_C) = m_B`, hence `q(m_C^n) = m_B^n` and `q^{-1}(m_B^n) = J + m_C^n`. Since completeness makes `B` adically separated, intersection of the powers of `m_B` is zero; taking inverse images gives `J = intersection_n (J + m_C^n)`. Thus `J` is closed, `J^1` lies in the ideal of definition, and the identity of `B` is continuous. The resulting section makes `B` an `A`-module retract of `S/IS`.

The two new unsplit statements are proper inputs rather than restatements of the target: 07ED changes the topology by completing both rings, while 07NN constructs the Cohen presentation used in the proof. Small cases were checked: for identity maps the presentation and retract reduce to identities; for `I=0`, `S/IS=S`; and completion does nothing to already complete rings.

The LeanSearch HTTP endpoint returned no response body during the new-node searches; those attempts are recorded as inconclusive. Loogle and source grep were successful. The Mathlib leaf was verified in the source at lines 171-174.

## Unfinished work

None in the claimed one-level split. The new 07ED and 07NN nodes intentionally remain `unsplit` for later Stage 1 work.

## Review by E1

I read More on Algebra Lemma 07NP (`lemma-formally-smooth-flat`) and its proof, plus 07ED (`lemma-formally-smooth-completion`), 07NN (`lemma-embed-map-Noetherian-complete-local-rings`), and 07NJ (`lemma-lift-continuous`) in `more-algebra.tex`. The item has the same Noetherian local, local-map, and maximal-ideal adic formal-smoothness hypotheses as 07NP. The two unsplit new statements reproduce the exact completion implication (07ED (1) to (3)) and the flat presentation clause of 07NN with their own rings and hypotheses. The retract node matches `Module.Flat.of_retract` at `Mathlib/RingTheory/Flat/Basic.lean:171-174`; I opened those lines. All three nodes are self-contained, use matching definition nodes, have single TeX escapes and exact tagged source labels. Searching the current DAG for 07ED/07NN and flat retract found an existing source-only completion node, `fs-adic-completion`, but its statement completes only the target while retaining the original source, so it does not supply the needed completed-source map. There was no equivalent flat-presentation or retract node.

Step 1 cites the completion, local-ring, Noetherian, and formal-smoothness statements that provide all properties needed to reduce to complete rings; local maps are continuous for their maximal-ideal topologies. Step 2 cites the precise 07NN square, and the factorization through S/IS is an elementary quotient calculation. Step 3 cites tensor-quotient base change and flat-module base change, with I the kernel of R onto A. Step 4 cites complete-local-quotient and the reviewed 07NJ lifting statement. For its application, q is surjective local, so its maximal-ideal image and every power equal those of B; B's separated completion makes J closed, and J is inside the ideal of definition with t=1. Step 5 cites the exact retract leaf; Step 6 cites faithful flatness of local completion, composition of flat maps, and flatness descent via a faithfully flat B-module. These cited statements give their uses without taking facts from their proofs. The source's section construction remains in the steps, rather than being put into a restatement node.

For E, I checked identity maps, I=0, and the already-complete case; the quotient and completion arguments still apply. I returned Step 4 to the worker under E5 because it initially inferred J was closed without identifying the quotient filtration. The worker added q(m_C)=m_B, q(m_C^n)=m_B^n, and the inverse-image calculation, then reran the split and DAG checks. The repair resolves the issue; I found no remaining A-F issue.
