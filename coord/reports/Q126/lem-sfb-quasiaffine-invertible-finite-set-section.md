## Worker report

Item: lem-sfb-quasiaffine-invertible-finite-set-section. Group: Q126. Stage: 1. Direct delivery. Resumed after the launcher pause; there was no earlier sandbox split, report or delivery process to reuse.

### Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-quasiaffine-invertible-finite-set-section.json`: split into seven steps; statement unchanged; no Mathlib match for the whole item.
- `citations.json`: fourteen records, one for every step/node citation, each quoting the cited statement verbatim.
- `report.md`: this report and the direct-worker review below.

## New nodes

None. There are zero new nodes and zero new Mathlib leaves. All supporting facts already have DAG nodes. The searches initially explored a possible quasi-affine ampleness input; reading the existing principal-comparison-cover statement showed that its identity-open-immersion specialization supplies exactly the required affine global-function cover, so no such new node was created.

## Attachments

None for the item. Searched the live `lean/WeilConjectures/` for the blueprint tag and the quasi-affine/invertible/finite-section notions. No project declaration found there states the whole item. The existing nonvanishing-locus, finite-generating-family and global-generation-cover declarations are supporting results only, not attachments of this item.

## Literature and searches

WANTED: none.

Read Stacks `properties.tex`, Tag 0F20, `lemma-quasi-affine-invertible-nonvanishing-section`, statement and complete proof. We need only the nonvanishing assertion with W=X, so the proof need not construct an affine nonvanishing locus contained in a smaller prescribed open. Read the cited preparation in Tags 01QE (`lemma-quasi-affine-O-ample`), 01Q3 (`proposition-characterize-ample`, especially (1) implies (7)), and 0ARY (`lemma-cartesian-diagram-quasi-affine`, proof), as well as `lemma-quasi-affine`. Read `modules.tex`, Tags 01AM (`definition-globally-generated`) and 01CY (`lemma-s-open`, statement and proof).

Read the chapter and unit records and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` direct-image proof. This auxiliary lemma remains below the already-selected line-bundle/divisor prerequisite. No chapter or unit route is replaced. The inherited ancestor metadata is retained; `blueprint_refs.py ancestor` reports a null imported ancestor for this created-node chain, as in the live item. Searches of the whole imported blueprint for `01QE`, `quasi-affine ample`, `nonvanishing`, `finite set nonvanishing`, `globally generated`, and `quasi-affine` found no imported statement equal to this item. All search results were read. Whole-DAG keyword and Stacks-tag searches found the supporting nodes used below.

Retained the item's inherited Mathlib searches and their actual recorded results. All additional Q126 Mathlib requests used the required `msearch.py` command and are in `searches.jsonl`; the node records the identical tools and queries. Two phrasings were tried for the quasi-affine preparation, followed by the full finite-set line-bundle assertion. The full-assertion LeanFinder hits were local-fraction and scalar-structure-sheaf lemmas; Loogle and grep gave no hits; LeanSearch gave quasi-affine basic-open and scalar zero-locus results. None states the item. The useful preparation hit `AlgebraicGeometry.Scheme.IsQuasiAffine.isBasis_basicOpen` was read in `Mathlib/AlgebraicGeometry/QuasiAffine.lean` (declaration begins at line 61); its statement only concerns affine basic opens, and the more detailed existing DAG node already supplies what is used. No search was recorded without running it, and none of the Q126 services returned an unavailable response.

## Not duplicates

No new-node/existing-node pairs arise. In particular, `lem-sfb-affine-invertible-finite-set-section` covers only affine X and cannot replace the present item for a general quasi-affine X. Its scalar-separation supporting node is reused on an ambient affine scheme, not misapplied to X. The principal-comparison-cover node supplies the needed quasi-affine preparation, so it was cited instead of duplicating it. The ample-twist, invertible-fibre and nonvanishing-open facts were also found and reused rather than restated as new nodes.

## Findings and corrections

The imported item is true, well typed, and faithful to the stated nonvanishing consequence of 0F20. There is no statement dispute or statement change. The live node had no proof. The substantive additions are the global-generation preparation and the complete induction. In particular, I did not apply the affine fibre-correction node to a quasi-affine scheme; that node's affine hypothesis would not hold. The replacement is the elementary calculation in step 7, using the section supplied by step 3 and the ambient affine separator supplied in step 6. No new premise such as Noetherianity, closedness of the points, irreducibility, reducedness, or infinitude of residue fields has been added.

The global-function cover, ample-twist global generation, global-generation fibre cover, and openness of the nonvanishing locus are generic tools from other units. The split declares their uses in `split_report.tool_uses`, with the specific statements taken from them. No top-level maintainer `tool_uses` field was written. These tools realize the preparation explicitly used in the proof of 0F20 rather than substitute another unit's proof route.

## Review by Q126

I read the node files and the sources open alongside this split. For the item, 0F20 assumes a quasi-affine scheme and an arbitrary invertible module, with an arbitrary finite set of points inside an open. The item makes the quasi-compact-open-in-affine meaning explicit and takes W=X. Its fibre quotient is the residue nonvanishing used by Modules 01CY. Thus every hypothesis and the retained conclusion agree with the source. No new nodes require a separate statement-only/source review.

1. Step 1 uses the *statement* of `lem-a1-quasi-affine-open-principal-comparison-cover`, specifically its final affine cover assertion. With U=V=X and the identity open immersion, the hypothesis on V is exactly the item's quasi-affineness hypothesis. This gives global functions with affine unit-germ opens; I did not take the charts from that node's proof. `lem-weil-pbc-basic-open-function` explicitly equates unit germ, germ outside the maximal ideal, and nonzero residue value. `def-sc-invertible-module` makes O_X invertible via its identity frame. `def-weil-pbc-ample-invertible-module` requires quasi-compactness and an affine nonvanishing open of some positive tensor power at every point; quasi-compactness is given and exponent 1 suffices. This spells out the forward 01QE input, using existing statements.

2. Step 2 uses the exact hypotheses of `lem-weil-pbc-coherent-twist-global-generation`: an ample invertible twisting module and a finite type quasi-coherent module. The first is O_X by step 1. Invertibility of L includes quasi-coherence in `def-sc-invertible-module`, and its local rank-one frame is a surjection from one copy of O, meeting the finite-type clause of `pqf-def-coherent`. The cited global-generation theorem is not restricted to Noetherian X or coherent L. Its conclusion really gives finite global generators for every sufficiently large nonnegative exponent. The tensor-product definition is `def-pur-sheaf-tensor-product`; the written multiplication/insertion-of-1 maps are inverse balanced maps commuting with restrictions, so the reduction of L tensor O^d to L does not hide a comparison lemma. A sheaf isomorphism takes the generating local linear combinations to generating combinations.

3. Step 3 cites `lem-sc-global-generation-nonvanishing-cover`, whose statement says precisely that all nonvanishing loci of global sections of a globally generated invertible module cover X. L is invertible by hypothesis and globally generated by step 2. Its explicitly defined locus is germ outside mL, so membership is exactly nonzero in the quotient occurring in the item. This supplies a section at a *single* arbitrary point; it does not assume the simultaneous conclusion being proved. No affine evaluation-surjectivity assertion is being inferred from mere local freeness.

4. Step 4 states strong induction on the cardinality and its base, with X,L fixed. Zero is a genuine global section even on the empty scheme, and with E empty there is no nonvanishing assertion to check. There is no lemma citation in this elementary step.

5. Step 5 uses only the open-locus clause of `lem-weil-pbc-nonvanishing-section-trivializes`; the statement indeed gives openness for any invertible module on any scheme, not just affine schemes. The induction hypothesis applies to E minus the *generalizing* point x, retaining its distinct specialization y. The direction is checked: y in the closure of {x} means that any open containing y contains x. Thus the nonvanishing section on y also works on x. Removing the specializing point instead would be incorrect, and is not done.

6. Step 6 uses the affine hypothesis of `lem-sfb-affine-finite-point-scalar-separation` on Y, not on X. F is finite, and the preceding case leaves no specializations between distinct points of E. The statement of `def-weil-open-immersion` is the homeomorphism onto an *open* subspace and identification with the open subscheme. Therefore a neighborhood of z missing x has image open in Y, which verifies the separation hypothesis on j(F),j(z). The scalar-separation node's statement supplies zeros at every old point and a nonzero value at the new point, including F empty. For restriction of the scalar, the same open-subscheme identification gives isomorphic stalk rings; quotienting by their maximal ideals gives exactly the residue-field comparison defined by `def-weil-residue-field`. Thus the claimed zero/nonzero values survive restriction. No assertion that image containment alone factors a morphism is used.

7. Step 7 cites the field clause of `def-weil-residue-field` and uses the already established singleton section of step 3. The formula v(w)=s(w)+f(w)t(w) follows by taking germs and quotients of a module section. At old points f vanishes, so no cancellation issue occurs. At z, s vanishes and f(z) is an invertible scalar; multiplication by its inverse proves that the nonzero t(z) stays nonzero. This is a two-line module-over-a-field argument, so it is elementary and does not become a new fibre-correction node or a restatement of the item. It works over finite fields as well.

I checked B1–B7: there are no new unsplit nodes with proofs; all notation in the unchanged item is introduced; all cited definitions actually define their notions; the added text uses single TeX escapes; Stacks sources include the correct tags and labels; no Mathlib leaf is claimed; and no statement delegates its meaning to a tag. For C1–C5 I opened every cited statement and made fourteen verbatim citation records; the above reading identifies the clause actually used in each case. The full dependency closures of the generic tool candidates do not reach this item, so they create no cycle. D1–D5 are addressed by the explicit induction and fibre calculation: nothing is moved into a restatement node and no omitted source argument is left behind. For E1–E6 I checked the exact affine, quasi-compact, finite-type and specialization hypotheses as detailed above. I found no E7 source error.

Small cases checked: X empty; E empty with X nonempty; a singleton; F empty in the induction; two incomparable points over a finite field; a generic point and its specialization (the generalizing point is removed); nonreduced affine charts; and a non-affine quasi-compact open of an affine scheme. No step requires a point to be closed. None of the seven steps exceeds 2000 characters, and none hides a lemma in a long inline argument. No Lean was written and no compiler, Lake or local server-only validation script was run.

## Unfinished work

The stage-1 split and self-review are complete. No mathematical gap is left in the item's assembly proof; existing supporting nodes retain their own statuses. The prescribed server preflight passed in the dry run; see the validation record below.

## Validation

The prescribed `deliver.py Q126 lem-sfb-quasiaffine-invertible-finite-set-section --no-push` exited 0 and printed `OK (not pushed)` at `e414826ec33`, with server preflight passed. No diagnostics required repair. After recording this result, the final report snapshot is checked again before the direct delivery push.
