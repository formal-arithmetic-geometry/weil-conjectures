# Stage-1 delivery: lem-sfb-etale-generic-component-splitting

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-etale-generic-component-splitting.json`: statement, split; statement unchanged, nine proof steps, no Mathlib match.
- `citations.json`: one verbatim statement quotation for every step/node pair.
- `report.md`: this report. `searches.jsonl` contains the searches executed by msearch.py; `prepare.py` is sandbox-only preparation material.

New nodes: 0. New Mathlib leaves: 0. The proof uses existing Mathlib leaves, but none is newly delivered. No unit realization fields need changing: this item is a supporting lemma, not the unit statement.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact item id and docstring tag, generic/component/splitting terminology, and Tag 0551. `AlgebraicGeometry.exists_finite_etale_geometric_component_extension` in `AlgebraicGeometry/GenericComponentsSplit.lean:52` is only the field-extension input, already owned by lem-sbc-generic-components-split. `exists_etale_generic_residue_field_model` gives an etale neighbourhood but does not assert a finite surjective affine cover of an open, so it cannot attach this item. The whole item has no project declaration found.

## WANTED

None. All needed sources are present in literature/stacks-project/. No SGA source was used.

## Corrections and observations

The imported statement is correct and was retained, including its empty-generic-fibre convention and its absence of reducedness, Noetherianity, separatedness and flatness assumptions. It had no proof. The polynomial model is free and therefore flat, but the given morphism X to S is never assumed flat. The model B is irreducible, not asserted integral: over a nonreduced base its coordinate ring need not be a domain.

The existing lem-weil-pbc-spread-finite-separable-extension assumes a Noetherian domain and cannot serve as the spreading input here. The existing lem-trf-finite-etale-generic-component-splitting also assumes an integral Noetherian base, so it cannot prove this item. Instead the proof keeps the actual monic-polynomial construction of Stacks 0551, using its already-existing smaller inputs.

The live item's blueprint.from.node is null. `python3 tools/blueprint_refs.py ancestor lem-sfb-etale-generic-component-splitting` also returns None. I preserved this existing provenance and its full from.place/via chain, filled same_as with the empty search result, and recorded the current blueprint location in split_report. I read the current latest sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and its direct-images proof, especially (3); no chapter/unit route was replaced.

## Not duplicates

No new nodes were created. DAG searches by 0551, 054R, polynomial lift, nilradical, monic quotient, fibre etaleness, flatness, finite closed maps and generic fields found all required inputs. Blueprint searches for 0551, geometrically irreducible, generic components, monic and residue field produced no blueprint node stating this full result. The broader search hits were read rather than copied into new nodes. The three nearest overlapping nodes differ as follows: lem-sbc-generic-components-split treats schemes over a field only; lem-sbc-etale-generic-residue-field-model gives no finite/surjective model over an open; lem-trf-finite-etale-generic-component-splitting has stronger integral Noetherian base hypotheses. All are pre-existing, and no competing node is proposed.

## Mathlib search assessment

The msearch.py log records actual LeanFinder, LeanSearch, Loogle and grep calls. Two formulations were tried: the full geometric splitting statement and the smaller residue-field extension/model question. The geometric hits give scheme etaleness, finite fibres, normalization, integrality and generic-point transport; they do not give this existence theorem. The algebraic hits include Algebra.exists_etale_of_isEtaleAt, residue-field finiteness, and Algebra.FormallyEtale/Etale field-extension characterizations; these are ingredients, not a one-line specialization giving a finite surjective irreducible affine model and split generic components. Loogle returned no hits for the combined patterns and grep returned no hits for the full-result pattern. Queries, returned names, digests and verdicts are recorded faithfully. The existing searches imported with the node were retained.

## Review by Q157

I read more-morphisms.tex Tag 0551, label lemma-make-components-generic-fibre-geometrically-irreducible, including all seven clauses and its proof. I read varieties.tex Tag 054R (lemma-finite-extension-geometrically-irreducible-components), algebra.tex Tag 00UD (lemma-make-etale-map-prescribed-residue-field), whose polynomial scaling is used in 0551, and Tag 00U6 (lemma-characterize-etale). I also read morphisms.tex lemma-etale-flat-etale-fibres, Tag 02GM, and the relevant finite/etale-map source locations. There are no new nodes needing their own source review. I opened the statements of all 26 nodes cited by the item, and citations.json contains their actual statement text, rather than a paraphrase of what a proof elsewhere suggests.

Step 1 uses the affine-open basis, the Mathlib nilradical criterion and finite-type base change. The nilradical criterion really permits arbitrary commutative rings and forces properness of the prime; its zero-ring exclusion matches the chosen nonempty affine open. The remaining generic-point claim is the direct equality V(p)=Spec A. The scheme fibre and residue-field definitions supply the actual maps.

Step 2 uses the full arbitrary-field-extension clause of lem-sbc-generic-components-split, not merely component descent to a separable closure. The finite-morphism definition gives module-finiteness for the whole affine field spectrum, and the etale residue-field lemma supplies separability of the same extension. The field spectra have their stated residue fields by def-weil-affine-spectrum. Only then is the primitive-element theorem applied with both of its hypotheses established.

Step 3 uses the exact monic minimal-polynomial lift, including its c outside p and its scaled generator. It does not infer this stronger lift from existence of an arbitrary integral multiple. Scaling by a nonzero field element preserves the generated field. Monicity survives passage to the nonzero residue field, so d is positive. The power-quotient tensor-coordinate node explicitly states faithful flatness; the proof does not ask the bare definition of flatness to prove it. The flat-affine criterion and finite-ring-map spectrum criterion give the scheme properties. Local finite presentation is witnessed by the actual polynomial presentation, exactly as its definition requests.

Step 4 uses finite-morphism permanence to make the scheme fibre affine and the affine-fibre tensor statement for its sections. The latter really allows arbitrary rings and arbitrary primes. The two algebra identifications are written as mutually inverse maps and the evaluation-kernel calculation, not attributed to the mere fibre definition. The fibre definition supplies the homeomorphism with the set-theoretic fibre, so Spec L gives uniqueness of q. This step is elementary assembly of cited affine results and the displayed quotient calculation.

Step 5 applies the flat-fibre etale-neighbourhood statement with the flatness and local finite presentation proved in Step 3 and the actual etale fibre of Step 4. Its statement is pointwise and imposes no Noetherian condition. The finite closed-map node explicitly gives closed images of arbitrary closed subsets, which is exactly what removes the non-etale complement. The affine-open basis is applied inside the open complement of Z, ensuring the shrunken base remains affine and contains p.

Step 6 uses finite base change and the affine-target clause to obtain an affine B. Etale base change is applied to W to U: B lies in W by construction of Z. Closedness of g(B), not a claim that an arbitrary dense open image is all of U, proves surjectivity because the image contains the generic point.

Step 7 uses the etale open-map theorem exactly for images of open subsets. Every nonempty open of U contains p, and its unique preimage forces q into every nonempty open of B. This establishes genericity and irreducibility by the elementary closure argument. It avoids any unproved claim that a polynomial quotient over a nonreduced base is a domain.

Step 8 uses the affine-stalk-localization statement, which includes compatibility of the germ maps, to keep the field map K to L. Localizing the field fibre at its only prime gives D_q/pD_q=L. Since D_q is local, that ideal is its maximal ideal. Thus the residue-field definition gives exactly L, not an unspecified isomorphic field with forgotten structure map. Restricting to B preserves the local ring at q.

Step 9 uses the actual pullback and scheme-fibre universal properties to identify the generic fibre over L, including its two projections. Repeating that same universal construction after every E/L ensures the inverse-image subsets correspond. Homeomorphisms preserve the maximal-irreducible-subset definition, so Step 2 supplies the full conclusion. This is elementary pullback assembly, not a new geometric-irreducibility comparison theorem.

I checked delivery-errors B--E individually: no new unsplit statement contains a proof; no notion was assigned an unrelated definition; sources name Stacks tags and labels; no unrun search is recorded; no unsupported attachment was made; every non-elementary input is a cited existing statement; no proof is hidden by moving the item into a new node; all hypotheses in each application are established in prior steps. I checked the cited-input dependency closures against the item to avoid a cycle. Every step is shorter than 2000 characters.

Small cases checked: S=Spec k, a degree-one extension (F linear), nonreduced S such as Spec(k[epsilon]/epsilon^2), an arbitrary irreducible non-Noetherian affine base, X empty, and a nonempty X with empty generic fibre. For the last two, the component assertion is vacuous while the independent polynomial cover remains nonempty. No finite family of components is selected from a fibre that might fail Noetherianity: the field-splitting input alone handles finite type over K. The zero ring cannot be the selected base ring because V is nonempty. No statement dispute was found.

Generic off-unit inputs are declared in split_report.tool_uses with their role: they are algebraic-geometry tools used to realize the existing 0551 input, not changes to the unit's six-functor route.

## Unfinished work

None in the stage-1 split. Stage-2 Lean and stage-3 proofs are outside this delivery.
