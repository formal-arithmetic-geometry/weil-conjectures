# Worker report: det-pe-wlocal-components

## Files written

- dag/nodes/sec-proetale-coefficients/det-pe-wlocal-components.json: statement, split into seven proof steps; no Mathlib match for the whole item.
- citations.json: every step/node pair with the verbatim statement it uses.
- No new nodes and no new Mathlib leaves. The searches were run with msearch.py and are recorded without invented queries; searches.jsonl is the command's own log.

## Attachments

WLocalSpace.isHomeomorph_connectedComponents_closedPoints, WLocalSpace.closedPointsHomeomorph, and WLocalSpace.closedPoints_eq_of_mk_eq belong to the existing node lem-weil-pbc-w-local-closed-points-components-homeomorphism, which already has a closed slopmaster2 audit. These declarations cover only part of the item, so the whole item is not an ATTACH. Read WeilConjectures/Topology/SpectralSpace/WLocal/{Basic,ClosedPoints,ConnectedComponents}.lean. ClosedPoints assumes WLocalSpace and therefore does not itself establish clause 1 under its weaker hypotheses. No declaration under the item blueprint tag was found. The whole-item searches and the second phrasing found structure declarations and profinite constructors, not the four-clause result.

## WANTED

None.

## Problems corrected

The imported proof had no dependencies, elementary=null throughout, and cited Tag 096A as a continuity theorem, although 096A is the definition of w-local. Continuity is now proved by writing the retraction as the inverse of the canonical closed-points/components homeomorphism composed with the quotient map. All non-elementary inputs are existing cited node statements. The first clause is proved without assuming unique closed specializations. The statement is unchanged, with its five actual statement dependencies recorded.

The imported item has no chapter/unit fields, and the corresponding chapter and unit JSON records are absent from dag/chapters and dag/units. I read the current main-20261015 chapter and unit _section.md files instead. I have not installed or changed maintainer metadata. The item is not the unit's definition/key node, so no realized fields are due.

## What remains unfinished

Nothing in this one-level split. No Lean was written or compiled. The second reader still reviews and delivers; this worker only runs --no-push.

## Not duplicates

No new nodes. Whole-DAG and blueprint searches for closed points, w-locality, profinite spaces, spectral topology, closed specializations, constructible closure, and localization led to reuse of the existing nodes. In particular the existing w-local homeomorphism is reused, not restated as a new node. No theorem is moved into a new node.

## Review by Q64

I read the current blueprint statement, its separate proof file, the local-hierarchy unit, and the pro-etale chapter. I checked Stacks proetale.tex Tag 0968 (lemma-spectral-split), Tag 096A (definition-w-local) and its following paragraph, and the warning example 0969. For clause 1 I read topology.tex Tag 0905 (lemma-characterize-profinite-spectral), especially the implication from no nontrivial specializations to closed compact opens; its input is Tag 0903 (lemma-constructible-stable-specialization-closed). For closed subspaces and existence of closed points I checked Tags 0902 and 005E. For localization I read algebra.tex Tag 00E3 (lemma-spec-localization). There are no new nodes requiring additional sources, and no SGA source is used.

Step 1 uses lem-weil-pbc-spectral-closed-subspace exactly for spectrality of the closed subspace S. Singletons of S are closed because the same singletons are closed in T. The ambient closedness hypothesis is essential and present. Step 2 uses lem-weil-pbc-spectral-open-retrocompact-iff-quasi-compact for an open of the spectral space S, and def-weil-constructible-subset only for its defining single-term constructible expression. It then applies the one-member-family instance of lem-weil-pbc-spectral-proconstructible-closure-specialization; the statement really supplies a specialization from a point in U, and the T1 condition makes that specialization an equality. This supplies the non-elementary fact behind profiniteness without introducing a new node for a clause of the item. Step 3 uses only the basis, compactness and sobriety in def-weil-spectral-space. The T0, Hausdorff and total-disconnectedness deductions are written out by separating points with those clopens.

Step 4 uses lem-sc-quasi-compact-kolmogorov-closed-point on the nonempty closed singleton closure, not on a noncompact open subspace; T is compact and T0. The statement gives a point closed in T, as needed, not merely a point closed in an arbitrary subspace. Connectedness of a singleton closure is explained by density, so no unrecorded irreducibility theorem is needed. Step 5 uses the precise canonical-map statement of lem-weil-pbc-w-local-closed-points-components-homeomorphism, whose spectrality, closedness and uniqueness hypotheses are all checked. It does not borrow the proof of that node. The quotient-map identity and the calculation r(x)=c explicitly establish continuity, retraction and the fiber formula. The already proved profiniteness in step 3 then passes across this homeomorphism.

Step 6 uses only the two definitions sk-def-pe-wlocal and def-weil-pbc-w-local to compare terminology after deriving uniqueness from connectedness of the singleton closure. The second definition is affine: the agreement with it is asserted on affine spectra. Closedness is retained on both sides, and the argument does not claim it follows from uniqueness (0969 rules that out). Step 7 uses the exact localization-at-prime definition and the image assertion of lem-weil-pbc-localization-spectrum-embedding, whose arbitrary multiplicative-set hypotheses apply to R minus m. The equivalence of avoiding R minus m with inclusion in m, and the Zariski singleton-closure computation, are written out. Clause 2 already identifies that set with the component, so no new component/localization lemma is hidden here.

I checked each cited node's statement directly, and citations.json contains its verbatim text for each occurrence. Off-unit generic tools are declared in split_report.tool_uses; these do not change the unit's route. The homeomorphism node is already Lean-closed. I preserved all imported blueprint and flag fields and set same_as=[] because no other blueprint node states all four clauses (the local-hierarchy definition recalls some consequences but does not state this general spectral-space result).

For edge cases, the empty spectral space has empty closed-point and component spaces and all maps/claims are valid. A one-point spectrum satisfies the retraction and localization assertions, including a local ring with nonclosed primes. A finite disconnected union of local spectra checks the separate components. The zero ring has empty spectrum, so clause 4 has no maximal ideal to quantify over. Clause 1 was checked without uniqueness, for example a finite spectral space with one generic point specializing to two closed points: its closed-point subspace is discrete profinite but clause 2 is not applied. No statement correction or dispute is necessary. I checked delivery-errors B through E: no new-node form or duplicate issue, every non-elementary input is cited for its statement, no relabelled clause, no circular inference, no finiteness/Noetherian hypothesis silently introduced, and no unproved compatibility is hidden behind a transport claim.

## Second reading by Q64

- Item statement: checked against the blueprint node and its proof, and against Stacks proetale.tex Tags 0968, 096A, 0969; all four clauses and their hypotheses are retained, including closedness of $T^c$, the empty spectrum, and the affine localization clause.
- Step 1: checked against `lem-weil-pbc-spectral-closed-subspace`; its closed-subspace and closed-singleton uses supply exactly the asserted spectral and specialization facts.
- Step 2: checked against `lem-weil-pbc-spectral-open-retrocompact-iff-quasi-compact`, `def-weil-constructible-subset`, and `lem-weil-pbc-spectral-proconstructible-closure-specialization`; the one-member constructible family and the T1 equality argument are explicit.
- Step 3: checked against `def-weil-spectral-space`; the sobriety-to-T0, basis separation, clopen separation, Hausdorff, and total-disconnectedness deductions are the stated elementary argument.
- Step 4: checked against `lem-sc-quasi-compact-kolmogorov-closed-point`; it is applied to the nonempty closed singleton closure, with quasi-compactness and T0/Kolmogorov hypotheses supplied by spectrality, and connectedness is proved from density.
- Step 5: checked against the exact statement of `lem-weil-pbc-w-local-closed-points-components-homeomorphism`; the quotient-map composition gives the continuous retraction, fibers, and homeomorphism without using its proof.
- Step 6: checked against `sk-def-pe-wlocal` and `def-weil-pbc-w-local`, and Stacks Tags 0968–0969; existence and uniqueness are separated, and closedness is not inferred from uniqueness.
- Step 7: checked against `def-weil-pbc-localization-at-prime` and `lem-weil-pbc-localization-spectrum-embedding`, plus the explicit Zariski closure computation; $R\\setminus\\mathfrak m$ gives exactly the primes contained in $\\mathfrak m$.
- New nodes: none; therefore B1–B7, duplicate checks, and Mathlib-leaf checks have no new-node cases. The existing cross-unit homeomorphism node was read and cited by its statement only.
- Edge cases: checked the empty spectrum/zero ring, a field and one-point spectrum, finite disconnected unions of local spectra, and a non-w-local finite spectral example; no clause changes.
- Changes: none to the item, proof steps, citations, or search log; this second reading records the direct source and dependency checks and found no repair necessary.
