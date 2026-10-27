# Stage-1 report: lem-trf-sharpening-blowup-chart-comparison

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-sharpening-blowup-chart-comparison.json`: statement, split; no Mathlib match. Eleven proof steps replace the empty imported proof. The statement, statement dependencies, source, ancestry, and maintainer fields are retained.
- `citations.json`: verbatim statement excerpts for all citations in the item's eleven steps.
- `searches.jsonl`: actual searches recorded by the required launcher command. Existing item searches from 2026-10-22 remain in the node; the five actual searches of this session are appended.

New nodes: **0**. Mathlib leaves: **0**. All non-elementary inputs already exist in the DAG. No Lean file was written and nothing was compiled.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id, sharpening/monoscheme/Kato fan terminology, and blowup chart comparison terminology. There is no project declaration of this monoidal-geometric comparison. The available ordinary scheme blowup charts are different objects. Supporting declarations in `lean/Sheaf/` do not constitute an upstream attachment, and the definition/sorry records are not proofs.

## WANTED

None. The ILO volume is present in the read-only literature directory. Its PDF was converted to text only inside this sandbox.

## What changed and what was wrong

The item's proof was empty. The source ILO VIII, Lemma 3.1.25, says that (i) is obvious, proves (ii) by comparing blowup charts, and deduces (iii). Those short instructions needed actual arguments: inverse image of an ideal under quotient by units, finite generators, the direct-product chart and its saturation, the effect of changing splittings and representatives, localized overlap equalities, preservation of both group hypotheses, and induction on the ordered tower. These are now written explicitly. There is no statement dispute and no weakening.

The source's description of monoidal geometry supplies no Stacks tag for this result. I read VIII 3.1.3--3.1.25, printed pp.98--102, and the existing fs face-sharpening node's source in VI 3.7(a), printed p.75. Source places name the actual numbered statements rather than inventing a tag. The supplemental unit-splitting lemma has the additional hypothesis on the sharp group, which this item explicitly provides; it is not applied to arbitrary fine torsion-free monoids.

The current `literature/blueprint/latest/` snapshot is main-20261023-1620. Its `lem-trf-local-term-locality` statement and proof now follow Varshavsky's normal-cone argument and do not contain the old alteration/monoidal-resolution branch. I read the current unit and chapter and the ancestor's statement and proof. This delivery completes the supporting item already in the historical created.item chain, with its inherited chapter/unit and blueprint.from intact; it changes no chapter or unit route and claims no new realization of the current ancestor. Whole-blueprint searches for `sharpening`, `blowup sharpening`, `monoid saturation`, and `monoid units`, and whole-DAG searches for the source number and related terms found no alternative imported blueprint statement to cite as this item. No unit realization fields belong to this supporting lemma.

## Not duplicates

No node is created. The following existing results are reused: `lem-trf-fine-monoid-unit-splitting`, `lem-trf-integral-sharpening-group-exactness`, `lem-trf-fine-monoid-finite-saturation`, `lem-trf-fs-face-sharpening`, and `lem-trf-affine-fan-localization-sections`. The broader `lem-trf-sharpening-fan-bijection` depends on this item; it cannot be cited here without a cycle. The affine-lift descent, fan refinement, toric realization, and saturated fan lifting statements have different conclusions and are unnecessary for this chart calculation. In particular I did not create nodes that simply restate an item clause.

## Mathlib searches

Ran the required `msearch.py N5 lem-trf-sharpening-blowup-chart-comparison` command with two LeanFinder phrasings, LeanSearch, Loogle `"sharpen"`, and a whole-Mathlib grep. All services answered. Read every returned signature. The first semantic search returned ordinary scheme ideal-quotient and glued-subsheme maps; the second returned generic additive localizations and division-pair constructions. LeanSearch returned ring ideal actions/localization and condensed monoidal sheaves. These do not supply spectra of fine monoids, quotient by units of their structure sheaves, or saturated monoidal blowup towers. Loogle and the monoidal-geometry grep returned no hits. Nothing is recorded as unavailable or as a Mathlib match. Generic monoid localization definitions do not prove the comparison in one specialization.

## Review by N5

I checked the split against delivery-errors B--E with the cited statements and the ILO source open. There are no new nodes, so no standalone statement, definition-dependency, Mathlib-leaf-line, same-tag duplicate, or new-node proof obligation is hidden in the delivery. The existing item statement is unchanged. All formulas use single TeX backslashes after JSON decoding. The proof is an argument, rather than a reference to ILO or a relabeling into child clauses.

Step 1 uses the monoscheme and monoid/fan definitions for spectra, units and localization. The integral-sharpening exactness statement supplies integrality of the quotient and the kernel of its group map. The affine-section lemma explicitly identifies the sharpened sections and stalks with localized quotients and says their maps are localization maps. This is enough to identify the two sharpened affine models; no claim is taken from the proof of another node. The prime correspondence follows directly because an ideal is invariant under adding and subtracting units.

Step 2 checks both inverse equalities on ideals and both directions of finite generation. The sheaf identification is local using Step 1, and the naturality assertion is equality of ideals generated by the same image sections. Both empty and whole ideals are covered. The only inputs are the actual ideal/coherence/pullback definitions, rather than a theorem incorrectly inferred from a definition.

Step 3 verifies the hypotheses of the cited fine-monoid unit-splitting statement at the closed point of each affine chart: both ordinary and sharp group completions are torsion free because the item assumes this at every stalk. That node gives precisely a section and the product isomorphism over the sharp quotient. Step 4 then calculates the chart on generators, including all unit coordinates; it does not assume that a noncanonical splitting is globally available.

Step 5 proves the product-saturation identity by positive multiples. The finite-saturation lemma explicitly gives fineness and commutation with localization, and the affine-section lemma identifies the quotient sheaves, not just their global monoids. Step 6 writes the change of splitting as an additive homomorphism to the unit group, and the change of a center lift as a unit difference. These vanish after sharpening. No unexplained transport or independence assertion remains.

Step 7 proves the overlap equality by the two displayed fraction identities, uses exactly the localization compatibility in the finite-saturation statement, and uses the explicit gluing definition. The triple-overlap cocycle is equality of the same elements in the group completion. Thus the maps glue over the base and commute with restrictions, rather than being merely objectwise isomorphisms.

Step 8 checks finiteness of the cover, fineness of each saturated chart, and ordinary stalk groups separately. The fs face-sharpening node really states that the localized sharp quotient has finite free group completion; I apply it to the complement of a prime in a fine saturated chart. It is not applied to a nonsaturated original chart. This verifies closure in the full category needed for the induction.

Step 9 gives the base and step of the length induction, constructs each center by the already-proved ideal bijection, and establishes the canonical identifications through the prescribed chart construction. Steps 10--11 write the actual homomorphisms on fractions and their extensions to saturation. Positive multiples prove that those extensions land in the target saturation. Equality of these formulas under identity and composition supplies the compatibility at each recursive stage. No ordinary or saturated fiber-product theorem is used; the statement asks for recursive pullback. All original indices remain present.

I tested rank-zero and pure-unit monoids ($B=0$), a sharp monoid with no units, $\mathbf N\oplus\mathbf Z$, and the nonsaturated sharp monoid $\langle2,3\rangle$. In the latter, a whole-ideal saturated stage really replaces the monoid by $\mathbf N$ and must not be deleted; the induction retains it. For $B=\mathbf N^2$ with the ideal generated by $(1,0),(0,1)$, the two overlap rings of fractions are identified by inverting the opposite differences; the identity persists with an additional unit factor. Empty ideals are included only in the ideal correspondence, while blowup centers are nonempty. Empty spaces and length-zero towers are vacuous and covered. A chart may acquire new units; Step 8 uses its saturated face quotient, so it does not assume the old unit group stays the full unit group.

Every non-elementary input is an existing cited node and every cited quote was checked as a literal substring of its statement. The proof dependencies are precisely the union of step citations. All reused statements are in the inherited unit. The longest proof step is below 2000 characters; none hides a separate standard lemma. I corrected the initial draft to cite integral-sharpening exactness explicitly where its kernel description was needed, instead of leaving it implicit. The final server dry run is recorded below when available.

## Unfinished work

No mathematical subargument is left unfinished. Existing supporting nodes retain their own future proof obligations. This delivery is stage 1 only.

## Validation

The required server dry run exited successfully: `OK (not pushed) deliver/N5/lem-trf-sharpening-blowup-chart-comparison at 86dfc14cb74: preflight passed`. The delivery command ran the server preflight, including the DAG and split checks. An additional sandbox consistency check verified that the statement is unchanged, each citation quote occurs literally in its referenced statement, all cited nodes have the inherited unit, and proof_deps is exactly the union of the eleven steps' citations. No local checker or compiler was invoked. The report is finalized with this validation before the final dry run and push.
