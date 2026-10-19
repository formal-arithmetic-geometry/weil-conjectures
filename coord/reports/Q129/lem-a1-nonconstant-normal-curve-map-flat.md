# Stage-1 report: lem-a1-nonconstant-normal-curve-map-flat

## 1. Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-a1-nonconstant-normal-curve-map-flat.json`: statement split in seven steps; no change to the statement or statement dependencies; no Mathlib match for the item.
- `citations.json`: 24 verbatim statement excerpts, one per cited node per step.
- `report.md`: this report. `searches.jsonl` is the search command's own preserved log.

New nodes: 0. New Mathlib leaves: 0. All supporting statements already exist. No Lean, unit, chapter, coordinator, launcher or shared-source files were changed.

## 2. Attachments

None. I searched the read-only slopmaster2 `WeilConjectures/` source for the exact item id, normal curves, nonconstant maps and flatness. No project declaration states this exact result. The existing normal-local-ring and integral-scheme tools are reused by node id; their audit is not a new attachment claim. Upstream master is reference material, not proof evidence.

## 3. WANTED

None. All mathematical sources used are locally available.

## 4. Problems and corrections

The item statement is correct as imported: Stacks curves.tex, Tag 0CCK (`lemma-flat`) assumes exactly a nonconstant map of integral curves and normal target. The two-point image condition expresses nonconstancy. I kept the statement, existing metadata and all inherited search records. The empty proof is replaced by the proof of 0CCK, expanding its references and the missing generic-point argument. In particular, the generic stalk is a field, not a DVR: the proof explicitly handles both dimensions zero and one. There is no perfectness, smoothness, separability, rational-point, finite-map or finite-module hypothesis.

The unit and chapter were read. This supporting lemma supplies the automatic flatness used in the third paragraph of the current main-20261015 `lem-a1-finite-map-curve.proof.md`, through the differential criterion node. The proof does not replace any unit step. The generic scheme-dimension equality and the normal local DVR theorem are declared as tool uses for transparency; the latter already has a closed audit.

Searches of the whole DAG by tag, statement words and titles, and `tools/blueprint_refs.py search` for flatness, dominance, normal local rings and nonconstant maps found the existing supporting nodes. There is no second blueprint statement of this item. No candidate new node survived: local PID classification is a few-line application of the existing DVR criterion, the local-ring injection is a commuting germ square with already-cited field embeddings, and torsion-freeness is cancellation. Making these nodes would duplicate or package elementary steps.

The item's current Mathlib searches were made solely using msearch.py: LeanFinder in the curve formulation and the more general dominant normal one-dimensional formulation, Loogle for Flat and IsIntegral, LeanSearch for the curve formulation, and source grep. The results appear verbatim in searches.jsonl and are appended to mathlib_searches. I read Flat.lean:35–55,99–123 and SchemeTheoreticallyDominant.lean:59–95. The hits give definitions, flat stalk criteria, flat open immersions, normalization or flat base change. The subsingleton integral target instance needs a one-point target, so does not prove a curve statement. No service failure was recorded as absence.

## 5. Unfinished work

None in this one-level split. Existing dependencies retain their own status. No new unsplit obligations were introduced.

## Review by Q129

I read all of delivery-errors.md B–E and checked the written split against each applicable failure mode, with the cited node statements open. For the item I read curves.tex Tag 0CCK (`lemma-flat`) and its proof, varieties.tex Tag 0B8Y (`lemma-regular-point-on-curve`), morphisms.tex Tag 0CC1 (`lemma-dominant-between-integral`), and more-algebra.tex Tag 0539 (`lemma-valuation-ring-torsion-free-flat`), verifying the tag-label correspondence in tags/tags. I also read properties.tex Tag 04MU, morphisms.tex Tag 01T6, algebra.tex Tags 00FN and 00PD, and schemes.tex Tag 01IS. There are no new-node sources to audit.

Step 1 uses the integral, finite-type and dimension-one clauses of def-pc-curve; the generic-point existence and uniqueness of lem-sc-scheme-sober; the supremum convention of def-pc-dimension; and exactly the equality in lem-pc-scheme-dimension-local-rings. In particular I did not silently interchange ring and topological dimension. The generic points exist because each whole space is irreducible closed and nonempty.

Step 2 uses sobriety uniqueness to make closures of different specializations strictly different. The definition def-kun-topological-krull-dimension forbids the explicit length-two chain displayed in the proof. Continuity is part of def-weil-locally-ringed-space-morphism. A closed subset containing the generic point contains the entire source. Thus a nongeneric image of the generic point would force a singleton image; no closed-image theorem or unjustified image factorization is used. This is a short direct dimension/closure argument, not an uncited dominance theorem.

Step 3 checks the Noetherian hypotheses before the DVR theorem. The field is Noetherian directly from its ideals; def-weil-affine-spectrum states its spectrum is one point; pqf-def-locnoeth supplies the Noetherian affine cover. The precise conclusion of lem-weil-pbc-finite-type-over-noetherian applies to the finite-type structure map of Y. The selected chart has Noetherian coordinate ring, and lem-weil-pbc-affine-open-stalk-localization states exactly that its germ map is a localization. This matches every localization hypothesis of lem-weil-pbc-localization-noetherian. No assertion about local Noetherianity is taken merely from a definition.

Step 4 uses normality of the actual target stalk from def-sbc-normal-dominant-galois, and checks dimension one and Noetherianity before applying lem-sc-normal-dim1-dvr. The DVR definition explicitly gives a domain with every ideal principal. In dimension zero the prime-chain definition and the local-ring unit criterion prove the field case directly. This handles the generic point correctly and does not impose a closed-point hypothesis on it.

Step 5 uses clause 2 of lem-sc-integral-scheme-stalks-in-function-field twice. Its statement explicitly gives the injective germ maps to the generic field and the domain property of each stalk. It applies to arbitrary integral schemes, not only algebraically closed-field smooth curves. The top map is a map between fields because Step 2 identifies the image generic point. I wrote the inverse argument proving that this unital field map is injective. The equality of the two composites is checked on a representative section using precisely the restriction-compatible sheaf map in def-weil-locally-ringed-space-morphism and the description of stalk elements as germs in def-weil-pbc-module-stalk. This is the elementary expansion of 0CC1 (2) => (6), rather than a citation to a node that does not state it.

Step 6 writes out cancellation in the domain B with the injective map from A. The hypothesis and conclusion of lem-weil-pbc-pid-torsion-free-module-flat are exactly the resulting torsion-free A-module and its flatness. Its statement has no finite-generation assumption, so the proof works for arbitrary curve morphisms. Step 7 uses exactly the stalkwise condition of def-weil-flat-morphism; it is definitional.

I checked small cases: the identity and open immersions satisfy the argument; Frobenius on the affine line in positive characteristic is nonconstant and flat even though not generically etale, showing that no separability slipped in. A constant map to a closed point fails the two-point hypothesis and would kill a target parameter, so Step 5 correctly cannot apply. The normalization of the cusp in characteristic zero shows why normality matters: in the local normalization k[t]_(t), the ideal (t^2,t^3) becomes (t^2), of minimal generator number one, whereas it has two minimal generators in k[t^2,t^3]_(t^2,t^3); a faithfully flat local extension would preserve that residue dimension. Thus one cannot drop the normal-target hypothesis. The generic target stalk is a field and has dimension zero, as Step 4 allows. Empty or zero-dimensional schemes are excluded by the stated integral-curve convention.

Citations.json quotes were checked as literal substrings of the current cited statements. Every `uses` edge occurs in proof_deps, with no circular dependency intentionally introduced. Every step is shorter than 2000 characters; there is no concealed long comparison argument. No new definition, duplicated node, item-clause restatement, or source error is present. The first dry run rejected four short citation excerpts (under 40 characters). I replaced those excerpts with the full cited statements, and expanded the continuity, curve and field-embedding excerpts so the quotes show every clause used. The repaired split is submitted to the independent server dry run.
