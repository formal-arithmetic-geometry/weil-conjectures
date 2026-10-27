## Files written

- dag/nodes/sec-trace-formula/lem-trf-etale-blowup-chart-descent.json: statement item, split into seven steps using existing nodes; not a Mathlib leaf.
- citations.json: twenty-three verbatim statement quotations, one for every cited node in every proof step.
- report.md: this report. No new DAG nodes, no Mathlib leaves, no unit records changed.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint id and for blowup/descent concepts, then read Blowup/BlowupUniversal.lean. The closed project declarations supply components, not the whole item. In particular AlgebraicGeometry.Scheme.IdealSheafData.hom_ext_of_isInvertible_comap (current file line 1069) and exists_lift_blowup (1289) belong to the already attached thm-nagata-blowup-universal-property; there is no new attachment claim.

## WANTED

None. Read ILO, Travaux de Gabber, Expose VIII 3.4.5--3.4.10, printed pp.111--112 (PDF pp.117--118), and the local Stacks sources named below. No SGA source was used.

## Issues in the imported material

The item statement is retained without changing a hypothesis or clause. The hypothesis that E_i consists of non-zero-divisors is stronger than needed for ordinary blowups, but it is neither dropped nor used to impose a new condition. Its chart calculation works even for general chart denominators because a is a unit in the localization containing the chart ring.

The raw statement of thm-nagata-blowup-universal-property is a stale, self-referential fragment: “Under the data of [thm-nagata-blowup-universal-property]”. Its blueprint_update.statement and the latest blueprint file give the actual final-object statement for every T with invertible extended ideal. I read both, as well as the current closed Lean uniqueness theorem, which assumes precisely invertibility of I.comap t and equality of composites. The proof only needs uniqueness. Even the old statement's restriction to a chosen invertible quotient suffices: the quotient onto the specified extended ideal is forced by its inclusion in O_T and the canonical map from the original ideal. Step 4 explicitly verifies this, rather than silently taking a stronger conclusion from the old statement. The verbatim quotation in citations.json is from the literal old statement, as required; it is not a fabricated replacement. This discrepancy is reported upward here; I did not edit another node.

ILO's “All claims can be checked etale locally” is expanded, not treated as a proof. The flat-base-change comparison convention places X_i first, whereas this item places B first: the proof explicitly exchanges the two fibre-product factors. No normalization or log-scheme assertion is inferred from the ordinary-blowup calculation.

## Unfinished work

None for this stage-1 item. Existing statement-only dependencies remain their owners' items, as the one-level split contract requires. No Lean was written or compiled.

## Not duplicates

No new nodes were created. DAG searches by Tags 0805, 0806, 022C, 023Q and by blowup/chart/descent terminology, and whole-blueprint searches with blueprint_refs.py, found the existing interfaces reused here. In particular no new lemma restates a clause of this item or duplicates the chart generator, principalization, flat-base-change or fpqc-representability statements. The blueprint ancestor is lem-trf-local-term-locality; no blueprint node states this combined ordinary-blowup descent result, so same_as remains [].

## Mathlib searches

Preserved all six imported search records. Ran and read new searches using msearch.py under this exact item: two LeanFinder phrasings, LeanSearch, Loogle for "blowup", and two grep patterns. searches.jsonl records the actual responses; the item's new records preserve them. None was unavailable. LeanSearch's closest result, AlgebraicGeometry.descendsAlong_isomorphisms_surjective_inf_flat_inf_quasicompact, was checked at Mathlib/AlgebraicGeometry/Morphisms/FlatDescent.lean:93: it descends the property of an existing morphism under a surjective flat quasi-compact map, and does not construct the canonical compatible maps required here. IsLocalIso, read in Morphisms/LocalIso.lean:29, is a source-local open-cover notion, not this theorem. The other hits concern etale ring presentations, closed subschemes, or Proj maps; none states all clauses or yields them in one line. No new-node searches were needed.

## Review by Q137

I read the item's chapter and unit, the latest blueprint statement and proof of lem-trf-local-term-locality, and the ordinary-blowup part of its recorded alteration ancestry. This is the same geometric subargument for the parent lem-trf-log-blowup-normalization, not a replacement for the contracting-correspondence unit route. The sources for the actual expansion are ILO VIII 3.4.6, divisors.tex Tags 0804/0805/0806 and 02OS, topologies.tex Tags 022C/022D, and descent.tex Tag 023Q. There are no new-node sources to review.

For Step 1 I opened the statements of lemma-nagata-extended-ideal-affine-chart (extended ideal is generated by the image of I), lemma-nagata-chart-extended-ideal-principal (I A[I/a]=(a)), lemma-nagata-chart-generator-regular (multiplication by a injective), and prop-nagata-affine-blowup-chart-cover (the charts for a finite generating family cover). These give exactly the claimed local ideal and cover; multiplication C→(a) supplies the rank-one identification. No regular sequence, Noetherianity or integrality is assumed.

For Step 2 I checked def-weil-flat-morphism says that the target stalk S is a flat module over the source stalk R, and def-weil-pbc-flat-ring-map defines flatness by preservation of injections under tensor. Thus tensoring the actual map R→R given by a is a direct instance of a cited definition, not an uncited exactness theorem. The tensor identification R tensor_R S=S gives multiplication by the pulled-back a. I additionally cited lemma-nagata-flat-pullback-ideal-pow with n=1 for the image of the pulled-back ideal, and def-pc-module-pullback for its tensor formula; neither fact is taken from a definition that only gives a kernel. Successive inverse images are the same fibre product, so their defining kernels agree. This corrected a potential C4 gap in the first draft. I wrote out the local stalk argument, and the conclusion is local freeness of the ideal itself, including its inclusion in O_T. This routine calculation is marked elementary with its definitions cited.

For Step 3 I checked def-weil-pbc-etale-site allows arbitrary jointly surjective etale covering families of the identity object X. Thus lem-weil-pbc-fpqc-finer-than-etale applies without assuming X affine or quasi-compact. I opened lem-galois-fpqc-covering-base-change and checked its conclusion is a covering of every U after arbitrary U→S. Def-weil-pbc-fpqc-covering then gives flatness of each individual projection, including Z_ij→Z_i by base changing the cover along Z_i→X. This supplies precisely the flatness Step 2 needs. Neither affineness of overlaps nor quasi-compactness of individual covering maps is used.

For Step 4 I read def-weil-etale-morphism to obtain flatness, and both the statement and statement dependency of thm-nagata-blowup-flat-base-change, so its symbol bc_g is the specified comparison for flat g and a quasi-coherent ideal. I checked the factor order in def-nagata-blowup-flat-base-change-map. Each composite is an X-map. Step 3 proves invertibility on the common source before applying blowup uniqueness; the stale-statement issue and the forced quotient are addressed above. The independently chosen theta_i do not need a new compatibility hypothesis.

For Step 5 I read the complete statement of lem-weil-pbc-fpqc-representable-descent: it glues morphisms to any scheme from compatible maps on an fpqc covering, uniquely. It is applied once with target B for existence and once with target X for the equality over X. Def-pc-fibre-product really states that a map is determined by its two components; it gives the specified base change, not merely an unspecified local isomorphism.

For Step 6 I checked the two pullbacks have common source Z_ij and target B_ij, with all three components prescribed. Equality of their B-components is already proved, and equality of the other components is the structural fibre-product equation. Equality of inverse maps is elementary cancellation. This proves compatibility of the maps to Z before applying the same representable descent node with target Z. Thus the step does not use an unproved theorem that local inverses glue.

For Step 7 the inverse identities are checked on the two actual fpqc covers and then use only the uniqueness part of that same descent statement. The argument also proves uniqueness of the isomorphism with the specified restrictions. I checked all twenty-three citations against their literal statements and generated verbatim quotations from those files. The two off-unit, nonclosed scheme-descent tools are declared in split_report.tool_uses; the Mathlib base-change-cover tool and closed Nagata interfaces are already permitted tools. No long step exceeds 2000 characters.

I tested the empty base and empty covering (all claims vacuous, unique empty isomorphism), empty charts/zero ring (injectivity still holds and there are no points to check), unit ideal (blowup is the identity and uniqueness forces the given local maps), a single chart, a multi-chart nonprincipal ideal such as (x,y) in k[x,y], and non-quasi-compact X with an infinite etale cover. I also checked why flatness is essential to the pullback-ideal assertion: the nonflat map Spec(C/(a))→Spec C kills the regular generator and yields a zero ideal on a nonempty scheme, so it must not be used on arbitrary overlaps without the flatness already supplied in Step 3. The proof avoids that error. The seven proof steps assemble existing statements; no lemma has been moved into a new node or hidden behind a source citation.
