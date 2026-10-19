# Worker report: lem-trf-j2-affine-cover

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-j2-affine-cover.json`: statement, split into five complete steps; Mathlib searches find no J-2 affine-cover theorem. The statement, statement dependencies and existing blueprint ancestry are retained. Proof dependencies are the union of the step citations.
- `citations.json`: 17 verbatim excerpts, one for every step/node pair.
- `searches.jsonl`: the actual msearch log. The helper `write_split.py` is sandbox-only.
- `report.md`: this report.

New nodes: 0. New Mathlib leaves: 0. All supporting facts already exist, including the Mathlib pointwise finite type criterion that makes a separate affine Spec criterion unnecessary.

## Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` tree by the exact item tag, J-2, regular locus, and related affine-cover terminology, and checked the upstream name table. There is no declaration of the project stating this item. Occurrences of `J.2` are projections from structures, not the J-2 predicate. Project uses of `HasRingHomProperty.Spec_iff` are applications within other arguments, not declarations of this item.

## Wanted literature

None. The Stacks sources required by this proof are present and were read locally.

## Audit and corrections

The imported item was unsplit with no proof and no Lean audit declaring an existing proof. Its statement is correct. I read Morphisms Tag 07R4, `lemma-J`, including the full equivalence and proof; its last paragraph proves (4) implies (1), and its second paragraph passes to finite type algebras on an arbitrary affine open, giving (3). The source's covering formula in (4) prints S instead of X; the item already explains this typographical issue. No statement correction or STATEMENT-DISPUTED is needed.

I also read More on Algebra Tag 07P7, `definition-J`, so the proof checks every finite type algebra, rather than just the regular locus of a chart ring. The locally Noetherian assumption is retained. No quasi-compactness of X, finite cover, separatedness, or affineness of an intersection is added.

The unit and chapter records were read first. The item is a component of `lem-trf-excellent-scheme-affine-cover`, used below the existing spreading/normalization branch of `lem-trf-local-term-locality`. It does not state the unit proposition and requires no edit to a unit's realization. The ancestor and via list are preserved. Whole-blueprint searches for J-2, regular locus, excellence, finite type ring, and Tag 01T2 gave no duplicate J-2 statement. DAG searches by the same notions and tag found the existing pointwise and all-affine-pairs criteria and the other tools used here. The two blueprint excellence results concern strictly henselian excellent DVRs/branches, not this general local property. There is no change of unit route and no SGA source is used.

The five recorded item searches were actually run with msearch by Q39 and logged. Semantic hits concern locally Noetherian schemes and finite type affine criteria, not J-2. Loogle `"J2"` and grep `J.?2.ring|IsJ2|regular.locus|regularLocus` returned zero hits. I also searched the potential affine-Spec helper: LeanFinder and LeanSearch returned the finite type `HasRingHomProperty` instance, Loogle returned `HasRingHomProperty.Spec_iff`, and grep located RingHomProperties.lean:360 and FiniteType.lean:54. I read those declarations. Before making any helper node I found `lem-weil-pbc-lft-pointwise-criterion`; choosing the whole affine source and target specializes that existing statement immediately, so no helper is created. Those extra searches remain in the log, without being misrepresented as searches for a new node.

## Not duplicates

No new nodes are proposed. In particular there is no new affine-Spec lemma: the existing `lem-weil-pbc-lft-pointwise-criterion` supplies it by taking whole affine neighbourhoods. The separate existing `lem-weil-pbc-lft-affine-pairs` is used in the other direction, to get finite type on every actual chart pair.

## Review by Q39

I checked the split against delivery-errors B through E with the cited node statements and source text open. This is the author's self-review for direct delivery.

Step 1 uses the full statement of `pqf-lem-affine-open-locnoeth` with S=X and the chosen affine V, so R is Noetherian under the actual hypothesis on X. `def-weil-affine-spectrum` supplies the map induced by R to B and its global sections. The statement of `lem-weil-pbc-lft-pointwise-criterion` is an equivalence with existence of one affine pair at every point. Taking Y and V themselves proves its right-hand condition directly; I do not take an affine-Spec implication from the proof of the all-pairs node. The sources read are Properties 01OW, `lemma-locally-Noetherian`, and Morphisms 01T1/01T2, `definition-finite-type`/`lemma-locally-finite-type-characterize`.

Step 2 uses `def-weil-open-immersion` for the open inclusion. From the actual definition in `def-weil-closed-immersion`, the identity is closed (whole underlying closed subset and surjective identity sheaf map); factoring j through this identity makes it an immersion. Clause (2) of `lem-weil-pbc-immersion-base-change-lft` really says immersions are locally of finite type. Clause (e) of `lem-weil-pbc-proper-fp-permanence` really includes composition for **locally** finite type morphisms, without a quasi-compactness condition: no properness clause is invoked. `pqf-lem-locnoeth-lft` applies to f and X and makes Y locally Noetherian. The regular-local predicate is the first sentence of `def-weil-regular-scheme`; I do not use the equivalence about regular schemes in that definition. The corresponding Stacks statements read are 01T5, 01T3, and 01T6 in morphisms.tex.

Step 3 uses the affine-basis statement of `lem-weil-pbc-affine-opens-basis` inside each open inverse image, with point y. The existence of the inverse-image open is continuity of f. The cover follows since each chosen chart contains its indexing point. `lem-weil-pbc-lft-affine-pairs` gives a finite type ring map on the exact pair W_y, U_i because f is locally finite type and the former maps into the latter. The sources read are Schemes 01IT, `lemma-basis-affine-opens`, and Morphisms 01T2. In particular W_y is chosen within an overlap; the overlap itself is never assumed affine.

Step 4 uses exactly the J-2 sentence of `def-exc-excellent-ring` on the finite type A_y-algebra C_y; it needs neither the G-ring nor the catenarity clauses. Clause (c) of `lem-weil-pbc-affine-open-stalk-localization` identifies the localization of C_y at the point's prime with the local ring of the ambient Y, which is precisely what is needed. The source read is Schemes 01HV, `lemma-spec-sheaves`, especially (1) and (6); the node includes its open-subscheme transport. Preservation of regular locality under a ring isomorphism is written directly from the regular-local definition: ideals, prime chains and generating sets are identified. It is a few-line use of definitions, not an unquoted assertion that regular loci commute with an arbitrary morphism. Openness passes through an affine isomorphism and then through the inclusion of an open subset; the union argument is elementary topology. These are the actual details of Reg(Y) intersect W_y = Reg(W_y) used in 07R4.

Step 5 applies the same localization-to-stalk statement to the whole affine Y. It identifies the scheme regular locus with the set of primes at which B is regular local, using the first sentence of `def-weil-regular-scheme`. Since B was arbitrary, the J-2 sentence of `def-exc-excellent-ring` now gives exactly the conclusion. There is no replacement by a weaker J-1 conclusion.

For edge cases I checked the empty scheme/empty covering, an empty affine V (R=0), and the zero finite type algebra B. Unital algebras over 0 are 0, and their spectra are empty; the pointwise condition and the empty-union openness argument still hold. For nonreduced rings (e.g. a polynomial algebra modulo a square over a field) the argument does not suppose the regular locus is nonempty: it uses precisely its openness from J-2. Infinite I is harmless because no finite subcover is extracted. None of the local-ring comparisons assumes regularity or reducedness. No new statement is left to test separately. All five proof steps are under 2000 characters and each carries its argument; no non-elementary subclaim is left as an unreferenced standard fact. The source typo was already documented, and the only refinement made during my own review was eliminating the contemplated duplicate affine-Spec helper after finding the existing pointwise criterion.

## Unfinished work

None in this one-level split. No Lean file was written and no compiler, Lake, or build tool was run. Delivery validation is by the required server-side dry run.
