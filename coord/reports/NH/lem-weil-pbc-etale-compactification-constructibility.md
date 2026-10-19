# Stage-1 repair: lem-weil-pbc-etale-compactification-constructibility

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-etale-compactification-constructibility.json`: existing statement node, split. Replaced old step 6 by three steps supported by existing nodes; kept its route and updated the final reference to the renumbered affine-base conclusion.
- `citations.json`: a verbatim statement excerpt for every step/node citation, including the newly used existing Mathlib leaf `lem-weil-pbc-qcqs-over-affine`.
- `report.md`: this report.
- `searches.jsonl`: actual Mathlib search log produced by msearch.py. Five exploratory searches for restriction geometry and five searches for the item were run and read. No new nodes or Mathlib leaves are proposed.

## Attachments

None. The slopmaster2 blueprint-tag search found no exact declaration. The related `AlgebraicGeometry.Etale.boundedConstructible_rightDerivedLowerShriek`, in `WeilConjectures/SixFunctors/Etale/Derived/Finiteness/DirectImage.lean:343`, requires finite-type schemes over a field, an invertible exponent, and bounded constructibility. Its proof also invokes the sorried finiteness input in that module. It does not prove this arbitrary-qcqs, arbitrary-finite-ring, bounded-below statement. The existing stage-2 Lean record is retained verbatim, without treating a stated theorem as a finished proof. No Lean was written or compiled.

## Wanted sources

None. The proof and the relevant smaller inputs are present in the archived Stacks sources.

## Defects and corrections

The dedicated return entry in `coord/returns/NH.md` identifies old step 6 (2021 characters) as hiding lemmas. I retained the statement exactly and kept old steps 1--5. The old final step is unchanged except that its reference to the affine-base result now points to step 8.

The replacement is substantive: step 6 checks geometric restriction hypotheses using the existing affine-presentation theorem and the existing qcqs-over-affine theorem, rather than carrying a principal-localization proof of local finite presentation. Step 7 isolates the elementary consequence of exact restriction and the already cited affine-local constructibility equivalence. Step 8 carries the actual finite-cover induction, with its two non-elementary inputs supplied by the affine-intersection and relative Mayer--Vietoris nodes, followed by the cited long exact sequence and Serre theorem. All nine steps are below 2000 characters (maximum 1798). This is not an extraction of the item's conclusion into a new lemma.

## Not duplicates

No new nodes. A potential restriction-of-morphisms helper was investigated and rejected: local finite presentation on source opens follows immediately from the already existing `lem-weil-pbc-lfp-affine-opens-finite-presentation` applied to the same affine charts. Closed diagonals restrict by the already existing closed-immersion base-change clause of `lem-weil-pbc-proper-fp-permanence`. The source's qcqs property is precisely the statement of existing Mathlib leaf `lem-weil-pbc-qcqs-over-affine`. A new helper would duplicate these statements or package an elementary consequence. Likewise the cohomology restriction argument is three applications of existing statements, and the kernel/cokernel extension calculation is elementary once the long exact sequence and Serre theorem have been cited.

Blueprint searches included `constructible shriek`, `restriction constructible`, `open finite presentation`, `affine opens`, `constructibility`, and `Serre`, over the whole imported blueprint. I also searched the DAG statements for restriction, open immersions, finite presentation, spectral sequences, and constructibility, and read the relevant candidates. The field/allowable-coefficient and pro-etale preservation statements are not substitutes for this etale finite-coefficient statement. The item's `same_as: []` remains appropriate.

## Review by NH

I read Stacks `more-etale.tex`, Tag 0GL0 (`theorem-constructible-shriek`), including its proof: localization on the base, induction on source affine covers, a closed immersion into affine space, composition of affine-line projections, and the bounded-below spectral sequence. I also read the supporting passages 0F7I (`lemma-shriek-well-defined`), 0F7J (`lemma-shriek-composition`), 0F7L (`lemma-base-change-shriek`), 0GKN (`lemma-relative-mayer-vietoris`), 0GK3 (`lemma-qf-f-shriek-constructible`), and 0GKZ (`lemma-constructible-shriek-rel-dim-1`). In `derived.tex` I read 015J (`lemma-two-ss-complex-functor`); in `etale-cohomology.tex` I read 095E (`lemma-constructible-quasi-compact-quasi-separated`). For the repaired geometry I read `morphisms.tex` 01TQ, including its explicit final restriction assertion, and `schemes.tex` 01KU, 01KV, and 03GI. I read the current main-20261015 blueprint ancestor and the fixed chapter and unit records. This repair retains the existing Stacks route below that ancestor; it introduces no alternative purity or coefficient route.

For each proof step, I opened and read every cited node's statement:

1. The compactification-independence node gives the comparison for every chosen compactification; Nagata gives compactifications for separated finite-type morphisms to qcqs bases. Finite rings are Noetherian and killed by a positive integer by the explicit finite-set argument. No invertibility is asserted.
2. The permanence node supplies the qcqs ambient scheme. Extension-by-zero exactness and the exact-functor homology node give the cohomology identification. The module-category node really says Grothendieck abelian, and the direct-image definition explicitly covers constant-ring module sheaves and says additive left exact. The truncation spectral-sequence statement supplies the quadrant, stabilization, finite filtration, and abutment, not just an E2-page. The Serre statement supplies kernels, cokernels, and extension closure. Thus this is a finite-filtration argument for bounded-below input, with no boundedness-above assumption.
3. The affine-line input is exactly for an arbitrary affine base, finite ring, constructible sheaf in degree zero, and every compactification. It supplies the sheaf premise of step 2.
4. Relative affine-space coordinates give the factorization into relative affine lines; the composition node is stated for qcqs separated finite-type morphisms and chosen candidates. Intermediate affine schemes satisfy those hypotheses. The identity case uses the identity compactification.
5. The affine-chart theorem supplies a finite list of generators and relations, hence the closed immersion is finitely presented. The quasi-finite shriek node explicitly includes such closed immersions. Negative-vanishing for left exact functors between Grothendieck abelian categories keeps the intermediate object bounded below. The composition node then applies to exactly these candidates.
6. The affine-chart theorem applies to every affine open of the quasi-compact source open, because it is also affine in X. This proves local finite presentation without requiring any open to be globally affine. The proper-permanence node explicitly includes closed-immersion base change, so the restricted diagonal is closed. The qcqs-morphism node's quasi-compactness assertion only needs quasi-compact source and quasi-separated target, not an already established quasi-separated source. Consequently the restriction is separated finite type over an affine base, precisely the hypotheses of the qcqs-over-affine node. Once its source is qcqs, the same permanence node gives quasi-separatedness and hence finite presentation. This order avoids circular use of qcqs.
7. The exact inverse-image node is for module sheaves over an arbitrary constant commutative ring, not just abelian sheaves. Part (c) of the exact-functor node identifies restricted cohomology and preserves its lower bound. The affine-local equivalence has the required qcqs hypothesis, established in step 6, and its affine tests are literally affine opens of X. This short consequence is marked elementary and no duplicate restriction lemma is created.
8. The intersection node assumes separatedness over an affine base, which is exactly the case in force. It gives a cover of the intersection with at most m-1 affine opens, so both induction calls strictly decrease m. The relative Mayer--Vietoris node allows arbitrary chosen compactifications and bounded-below finite-ring complexes, with quasi-compact U and V. Steps 6 and 7 verify the restricted objects meet its hypotheses. The long-exact-sequence node gives the displayed five-term portion. Kernel and cokernel closure in the Serre statement give the two ends of the short exact sequence for the middle cohomology; extension closure gives the conclusion. No additional general gluing theorem is silently assumed.
9. The original base-change theorem explicitly allows the arbitrary open map W to Y, finite coefficients without invertibility, and the specified compact-support candidate. The geometry permanence statements ensure the base-changed source is qcqs. Exact inverse image and the exact-functor homology statement give the cohomology comparison; the qcqs affine-local equivalence gives the result on Y. Compactification independence returns to the originally fixed candidate.

I checked empty source and empty opens (m=0 and redundant empty members of a cover), the identity morphism and n=0 affine-space factorization, the zero ring, finite rings of residue characteristic, and complexes unbounded above but bounded below. Empty schemes give zero objects. No characteristic or field assumption is introduced, and in each total degree the spectral sequence uses finitely many entries. I compared the sandbox and shared item statements and Lean records for equality. Every cited quote is copied verbatim from the corresponding statement; citations.json covers every uses entry. There are no new statements to test or new source-tag duplicate pairs.

## Unfinished work

None in this one-level repair. Existing smaller statements remain their own DAG items; their proofs are not claimed here.

## Validation

Server checks and the required delivery dry run are recorded below after completion. No checker was run locally.

- Server `srvcheck.py ... review_split`: PASS, zero new nodes.
- Required `deliver.py NH lem-weil-pbc-etale-compactification-constructibility --no-push`: exited 0 and printed `OK (not pushed) ... at 88857500c7: preflight passed`. The delivery server ran preflight, including its DAG and split checks. No mathematical change followed this successful dry run; this paragraph records the result.
- Local JSON/citation consistency checks confirmed the unchanged statement and Lean record, nine steps shorter than 2000 characters, and 37 verbatim citation entries covering exactly the uses lists.
