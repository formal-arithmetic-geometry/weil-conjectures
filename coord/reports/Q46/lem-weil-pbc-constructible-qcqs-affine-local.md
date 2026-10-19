# Stage-1 report: lem-weil-pbc-constructible-qcqs-affine-local

Files written:

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-constructible-qcqs-affine-local.json` — statement, split proof, status `split`; no new nodes.
- `citations.json` — 17 verbatim statement citations covering every non-elementary use in steps 2–5.
- `report.md` — this report.

Attachments: none. I searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id and declaration name; no declaration was present, so there is no finished proof to attach.

WANTED: none.

The imported statement agrees with the main-20261015 blueprint node and with Stacks Lemma 095E/Definition 03RW for a finite coefficient ring. I retained the three clauses and the six-step proof. No new lemma node was needed: every non-elementary fact used by the proof is already stated by an existing DAG node, and the two implication-bookend steps are elementary.

## Review by Q46

I read the item node, the chapter `sec-proper-base-change`, the unit `sk-thm-p1`, and the blueprint ancestor `def-weil-pbc-constructible-complexes`. I also read the Stacks source `literature/stacks-project/etale-cohomology.tex` at Lemma 095E, Definition 03RW, and the cited constructibility/topology paragraphs. The source gives exactly the global/covering/affine-local equivalence used here; the finite-ring module convention is supplied by the existing finite-locally-constant module-values node.

Step 1 is the direct implication (1)⇒(2) by taking the one-open cover `{T}`, so it is elementary. Step 2 is the pullback and coefficient check: I verified that `lem-weil-pbc-etale-inverse-image-restriction` supplies the etale restriction comparison, `lem-weil-pbc-etale-covering-base-change` supplies an etale jointly-surjective pullback cover, and `lemma-constructible-pullback-constant` preserves the same constant module value. The module inverse-image definition, constant-sheaf definition, finite-locally-constant equivalence, same-image immersion invariance, composite-adjunction and conjugate-left-adjoint statements, direct-image formula, and the etale restriction statement all say the precise operations used in that step; their statements are quoted verbatim in `citations.json`. I checked the long step (2, 2222 characters) for hidden claims: its scalar compatibility uses naturality of the cited inverse-image/restriction comparison, its composition comparison uses the cited adjunction/direct-image formulas, and its reduced-stratum replacement uses the cited same-image immersion lemma.

Step 3 chooses affine neighborhoods using `lem-weil-pbc-affine-opens-basis`, takes a finite subcover by quasi-compactness, and transports each local partition. I checked the affine-basis statement and the stratification definition; the quasi-compact finite-subcover argument and the composition of immersions are elementary under the stated qcqs hypotheses.

Step 4 applies `lem-weil-pbc-etale-stratification-local-gluing-core`. I verified that its hypotheses are exactly a finite affine cover of a quasi-compact quasi-separated scheme and local finite constructible immersed stratifications, and that its conclusion supplies an actual morphism through a local stratum. The constructible-sheaf definition then gives clause (3), including the finite locally constant module condition. This avoids inferring scheme-theoretic factorization from set-theoretic image containment.

Step 5 pulls the global stratification back with `lemma-constructible-pullback-stratification`, proves constructibility inside an arbitrary affine open with `lem-weil-pbc-constructible-preimage`, and uses `def-weil-constructible-subset` for retrocompactness. I checked the required quasi-compact-open argument: a quasi-compact open of the affine chart is quasi-compact in `T`, so the inclusion has retrocompact inverse images. The cited pullback-stratification statement gives the strata and the cited preimage lemma gives constructibility; the finite-local-constancy transfer is the pullback argument from step 2. Empty intersections are allowed and no intersection of affine opens is assumed affine.

Step 6 is the elementary conclusion that the three implications establish the equivalence. I found no missing hypotheses, duplicate/new node, statement error, or source error. The Mathlib searches were rerun on 2026-10-17 with LeanFinder, Loogle, grep, and LeanSearch; they found only generic topology, finite-generation, and morphism-image results, not this etale module-sheaf equivalence.

What could not be finished: no Lean proof was written or compiled, as required for this stage-1 delivery.
