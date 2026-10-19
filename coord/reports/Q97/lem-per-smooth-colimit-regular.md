# Q97: lem-per-smooth-colimit-regular

## Files written

- `dag/nodes/sec-deligne-laumon-a1/lem-per-smooth-colimit-regular.json`: statement, split into six steps following Stacks 07EP; statement and statement dependencies unchanged. Mathlib searches found ingredients only.
- `dag/nodes/sec-deligne-laumon-a1/lem-per-noetherian-local-colimit-regular.json`: new statement-only unsplit lemma, Stacks 07DX. Mathlib searches found no matching theorem.
- `citations.json`: a verbatim statement quote for every cited node in every step.

One new node; zero new Mathlib leaves. No unit or chapter record changed: this is an auxiliary node, not the key statement of the perverse Fourier unit.

## Attachments

None. Read-only searches under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` for the item id, regular/smooth colimits, and 07DX/07EP gave no matching project declaration. No existing sorry declaration was treated as finished.

## WANTED

None. All sources used are present locally.

## Problems corrected

No statement correction or statement dispute. The supplied item is an accurate small filtered-category formulation of Stacks 07EP. Its existing search records and provenance were retained, and current searches are appended from this sandbox's actual `searches.jsonl`.

The original empty proof did not expose the hypotheses needed at the last Stacks citation. Stacks 07DX is about local rings and local transition maps, not arbitrary regular rings. Steps 4–5 explicitly localize at contracted primes, verify locality by testing numerators, and use Categories 0032 to obtain the directed-set index required by the new node. Step 2 also supplies Noetherianity after finite field extension, implicit in the proof of 07EP. No flatness of the transition maps is assumed or used.

The source route is unchanged: smooth flatness, tensoring the colimit to a finite purely inseparable residue-field extension, regularity of smooth algebras over a field, then regularity of the resulting Noetherian local colimit. No SGA source is used. The old provenance mentions an external strict-local reduction, but this delivery neither cites nor reads a forbidden SGA source.

## Unfinished work

None for this split. The new 07DX node intentionally carries only a statement and is left for the next DAG level.

## Not duplicates

lem-per-noetherian-local-colimit-regular vs lem-weil-pbc-field-regular-ring: the latter proves that a field is regular (the zero-dimensional base case mentioned in the proof of 07DX); it does not state regularity of Noetherian directed colimits of regular local rings with local transition maps.

lem-per-noetherian-local-colimit-regular vs lem-per-smooth-colimit-regular: the new lemma concerns arbitrary directed systems of regular local rings with local maps and a Noetherian apex; it assumes neither a base ring nor smoothness, and concludes local regularity. The item must still prove flatness and geometric regularity of every fibre after field extension, construct the localized diagram, and verify the Noetherian and local-map hypotheses. Thus the new lemma is the genuinely smaller independent local-algebra input 07DX, not a clause of the item's statement.

Whole-DAG searches by 07DX, the source label, and colimit/regular/local keywords found no node stating this lemma. The `field-regular-ring` source mentions the proof's dimension-zero sentence only. Whole-blueprint searches `07DX`, `regular local`, `regular colimit`, `colimit regular`, and `colimit-flat` found no duplicate. The regular-local blueprint results concern domains, DVRs, and definitions; none gives the colimit theorem. Project Lean searches likewise found no attachment. Mathlib was searched with both direct-limit and directed-colimit phrasings; hits on regular sequences, finite Krull dimension, and polynomial regular rings were read and do not state 07DX. The pinned RegularLocalRing/Defs.lean was inspected: it supplies definitions and permanence under isomorphisms, not a colimit theorem.

## Review by Q97

I read the chapter and unit records, the current main-20261015 ancestor statement and proof, the inherited strict-local-model statement, and the item source in `literature/stacks-project/more-algebra.tex`, Tag 07EP, `lemma-colimit-smooth-regular`, including the full proof. For the new node I read `literature/stacks-project/algebra.tex`, Tag 07DX, `lemma-colimit-regular`, statement and proof, and verified the tag-label correspondence in `tags/tags`. I also read the statements and relevant source passages of Algebra 00TT (smooth over a field), 045I (Noetherian field extension, although the finite case here is proved via module finiteness), and the tensor/localization definitions. The split uses the finite-algebra Noetherian leaf rather than the existing geometrically-regular-field-extension theorem: the latter requires geometric regularity and would be circular here.

For step 1 I opened all three nodes: smooth-ring-map-flat gives flatness with no Noetherian hypothesis, algebras-underlying-module explicitly supplies the module-colimit universal property, and filtered-colimit-flat-modules applies to a small filtered category. These are exactly the hypotheses here. Flatness is not inferred merely from its definition.

For step 2 the finite-purely-inseparable definition supplies a finite-dimensional field extension. Tensor-cancel-base-change gives the displayed algebra isomorphism with S=k and A=K. The tensor definition supplies finite sums and bilinearity, which make the finite-basis module-generation argument explicit. Finite-algebra-noetherian requires a Noetherian base and a module-finite algebra, both verified with base F. No assumption that the whole ring B is Noetherian is introduced.

For step 3 the tensor-elementwise node explicitly states a module-colimit universal property and representation by a stage, and asserts that the maps are ring maps for an algebra N. Its same-universe condition is addressed by taking a common universe. The upgrade to the ring-colimit universal property is written out using a common stage for two representatives, not taken from a definition node or an unquoted proof. This is one routine universal-property verification; it introduces no separate comparison lemma or hidden non-elementary assertion. The category-colimit definition is used only for that universal property.

For step 4 smooth-ring-map-base-change-composition clause (1) gives smooth K-algebras, and smooth-over-field-regular-local applies because K is a field. Localization-at-prime explicitly gives the localization diagram and its colimit. It does not say its transition maps are local, so the fraction test is supplied in the step: membership in the maximal ideal means the numerator belongs to the contracted prime. Localization-noetherian is applied only after C has been shown Noetherian. The localization definition supplies the description of maximal ideals; it is not cited as a substitute for the colimit theorem.

For step 5 I checked that filtered-category-directed-cofinal states preservation of the colimit for every category, and gives a nonempty directed set with arrows from J. Its directed reindexing therefore preserves the already proved locality of the maps. The new node needs precisely regular local stages, local maps, and a Noetherian apex. All three were verified in step 4. Applying it for each prime proves regularity of C using the regular-ring definition. Step 6 uses the geometrically-regular definition in g-ring, which tests finite purely inseparable extensions and requires a Noetherian fibre; this is exactly what steps 2–5 established. The same node defines the final regular map as flat with these fibres.

I checked delivery-errors B–E against these files: new node self-contained and statement-only, notions defined or inline, exact tag and label, no new definition, no new node restating a clause, no citation of a proof's private construction, no circular use of Popescu's theorem or geometric regularity, no dropped Noetherian/local-map/universe hypotheses. All cited statements were opened, and citations.json copies their actual text. Generic off-unit algebra statements are declared in split_report.tool_uses; these support the existing strict-local algebra reduction and do not replace any step of the unit's Fourier route. The proof steps are each below 2000 characters.

Small cases checked: R=0 (no primes and flat zero module), zero fibres (vacuously regular, with no prime localizations), a singleton diagram (ordinary smooth regularity), a field base, a trivial purely inseparable extension (which already tests regularity of the fibre itself), and noninjective local transition maps. The new lemma does not assume injectivity, flatness, or constant dimension; none is used in the item. It would be false to remove the Noetherian apex condition (for instance the local polynomial ring in infinitely many variables arises as a directed local colimit), so that condition is retained. Nonlocal transition maps are also not silently allowed.
