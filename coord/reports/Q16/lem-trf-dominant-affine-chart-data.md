# Q16 stage-1 delivery: lem-trf-dominant-affine-chart-data

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-dominant-affine-chart-data.json`: statement; split into seven steps; no full Mathlib match. The statement is unchanged.
- `citations.json`: 14 entries, one per step/node citation, quoted verbatim from the current DAG statements.
- `report.md`: this report. `searches.jsonl` is the search command's original log.

New nodes: 0. New Mathlib leaves: 0. Existing generic-point, spectrum-stalk and stalk-map leaves supply the substantive algebraic-geometric ingredients.

## Attachments

None. I searched `lean/WeilConjectures/` by the blueprint tag and by dominance, affine-chart and function-field terminology. There is no declaration of the entire item. The project contains the narrower generic-point lemma `AlgebraicGeometry.Scheme.Hom.apply_genericPoint_of_isDominant` in `AlgebraicGeometry/Morphisms/FiberDegree.lean`, the private generic-point/map constructions in `AlgebraicGeometry/Morphisms/DominantFunctionFieldLimit.lean`, and `AlgebraicGeometry.Scheme.Hom.functionFieldMap` in `AlgebraicGeometry/Curve/DivisorPullback.lean`. These do not supply every chart-selection and fraction-formula clause under exactly this item's hypotheses, so they do not justify ATTACH.

## WANTED

None. All sources used are present in the read-only repository.

## Findings and corrections

The imported item was a statement-only auxiliary of `lem-trf-local-dimension-formula`. I kept its statement, statement dependencies, source, ancestry and other ownership fields. I added the complete proof, proof dependencies, proof origin, split report and actual current searches. The source route is Stacks 0CC1, whose proof identifies generic points with zero primes, together with the affine reduction in 02JU. The fraction formula is justified through the existing Spec stalk-localization result, including its commuting germ square, rather than by choosing an unspecified field embedding.

No statement dispute was found. No source error or unit-route departure is needed. I read the chapter and unit records and the current main-20261015 ancestor text. This is an auxiliary inside the normal-cone dimension reduction under `lem-trf-local-term-locality`, not the key statement of `sk-i-curve-zero`, so its unit's realization fields are not changed.

## Mathlib and duplicate searches

The inherited searches are retained. New searches were made with the mandated msearch.py command and read as returned. Two LeanFinder phrasings did not locate the whole combined statement. Loogle with `AlgebraicGeometry.LocallyOfFiniteType, AlgebraicGeometry.IsDominant` returned no hit. The first grep found the germ injections and fraction-field material in FunctionField.lean; a second grep in FiniteType.lean only found essential finite type of stalk maps. LeanSearch was rate limited and is recorded as unavailable.

I read Mathlib's FunctionField.lean, particularly the germ injection, generic-point open-immersion lemma, and `functionField_isFractionRing_of_isAffineOpen`, and FiniteType.lean's affine-pair definition. The hits cover ingredients, not the whole combined item as a one-line specialization. The DAG already has the needed leaves: `lem-weil-pbc-spec-domain-stalks-function-field` and `lem-weil-pbc-spec-map-stalk-localization`. In particular I did not create a new lemma for any clause of the item.

## Not duplicates

No new node is proposed, hence there are no new/existing same-tag pairs. Searches of the whole DAG by 0CC1, the generic-point/function-field and affine-chart concepts, and `tools/blueprint_refs.py search` for dominant, function field, fraction field and affine chart found no other blueprint statement equal to this item. Definitions of canonical function-field maps and stronger or specialized curve assertions were not treated as statements of this whole result. The item's `same_as` remains `[]`.

## Repair of returned delivery

The return of 2026-10-22 07:24 UTC names head `7eaa58d0d69` and reports a landing refusal caused by a side completion that had not been promoted into the live DAG. It asks for a delivery rebuilt on the current DAG, a fresh reading of changed dependencies, and adjustment of the split. I retained the returned sandbox proof, citations, report and search log. I compared its item JSON with the current read-only repository: the current item is `unsplit`, with empty proof and proof dependencies; its statement, statement dependencies, source, ancestry and maintainer metadata agree with the retained version. No released repair note exists for this item. The delivery tool constructs a fresh commit on current `origin/sheaf-dag` and preserves the current maintainer-owned fields, so no side-project completion or old reviewed marker is supplied by this repair.

I re-read all ten distinct proof dependencies and the two further statement definitions of Noetherian ring and finite type algebra, rather than inferring compatibility from their ids. All fourteen retained citation quotes remain literal substrings of the current statements. In particular the spectrum-stalk lemma still states the fraction-field identification as an algebra identification using the germ map, and the spectrum-map lemma still states both inverse-image primes and the commuting germ square. The locally finite type definition still provides a covering over every chosen base affine. These are exactly the interfaces needed by the seven-step proof, so the statement and dependency lists need no change.

I adjusted Step 3 to give the two inverse maps on representatives and to write the stalk-map comparison on a section over an actual neighbourhood $N$ of $f(t)$: the original pullback on $f^{-1}(N)$ restricts to the pullback on $V\cap f^{-1}(N)$. This explicitly verifies the compatibility needed in Steps 4 and 6 against the present sheaf-morphism statement. The proof still uses the same two definition nodes at this step; no node, search, or mathematical hypothesis was added. I re-read Stacks 0CC1, 01T2, 01HV, 01HY, 01I1 and 01ON in the local TeX sources and rechecked the small cases described below. The initial diagnostic dry run exited successfully at `f87abc03138`; the adjusted files are submitted to a fresh final dry run before pushing.

## Latest landing-refusal repair (11:42 UTC, head 1e45b8620b3)

The latest return repeats the side-completion promotion refusal for head `1e45b8620b3`. The earlier 07:24 repair described above is retained as history. This attempt starts from the retained delivered sandbox; the current repository item is still `unsplit`, and differs from the sandbox only in the stage-1 split fields and accumulated searches. Its statement, statement dependencies, source, ancestry and ownership fields agree. There is still no released stage-1 repair note. The mandatory initial dry run completed successfully at `7b6b5468583`, rebuilding the delivery on the current server DAG rather than carrying a side-DAG reviewed marker.

I reopened all twelve distinct statement/proof dependencies in the current DAG. All fourteen entries of `citations.json` still quote their statements verbatim, and the citation set equals the union of the seven steps' uses. In particular the two Spec lemmas remain Mathlib leaves: one identifies stalks as localizations with their algebra maps, the other describes the prime preimage and the actual stalk map with its commuting germ square. The locally finite type definition still allows the affine covering over the prescribed base affine, and the Noetherian definition still requires only the base covering chosen in Step 1. No changed interface requires a new dependency or statement correction.

I adjusted Step 6 after this rereading: it now names the isomorphisms `i_A` and `i_B` from the localizations into the global generic stalks, specifies their values on `a/1` and `c/1`, writes the equation `f_eta sharp ∘ i_A = i_B ∘ phi_0`, and evaluates it to obtain the actual global germ square. This makes the connection between the current localization lemma and the fraction formula explicit. Step 3's section-representative calculation is retained. This is a proof-content repair, not an unchanged re-push; it adds no node, hypothesis or search question.

I reread Stacks 0CC1 (`lemma-dominant-between-integral`), 02JU (`lemma-dimension-formula`), 01T2 (`lemma-locally-finite-type-characterize`), 01ON (`lemma-characterize-integral`), 01HV (`lemma-spec-sheaves`), 01HY (`lemma-morphism-into-affine-where-point-goes`) and 01I1 (`lemma-morphism-into-affine`). They retain the same integral/dominant and affine localization route. The field-spectrum, localization and generic-point cases still satisfy every hypothesis; neither separatedness nor global quasi-compactness is used. Every non-elementary step is under 2000 characters. No new Mathlib searches were necessary: the statement and all search questions are unchanged, and I read the retained `searches.jsonl` results and the narrower upstream generic-point/function-field declarations again.

## Review by Q16

For this repair I performed the current-DAG comparison and source/interface review described above. The earlier Step 3 calculation on section representatives is retained. For the latest returned head I made Step 6 explicit with the two localization-to-generic-stalk isomorphisms, their compatibility equation, and its evaluation on ring elements. The other steps retain the reviewed argument.

I read Stacks morphisms.tex, Tag 0CC1 (`lemma-dominant-between-integral`), all six assertions and its proof, and Tag 02JU (`lemma-dimension-formula`), its hypotheses and affine-reduction proof. I also read the affine finite-type characterization 01T2 in morphisms.tex; the integral characterization 01ON and locally Noetherian characterization 01OW in properties.tex; and 01HV (6), 01HY and the construction in 01I1 in schemes.tex. The stalk colimit/germ rule is supplied by the existing `def-weil-pbc-module-stalk`, whose statement I opened, as I did every other cited node. There are no new-node sources to audit.

Step 1 cites `pqf-def-locnoeth`, which explicitly supplies a Noetherian affine covering, and `def-weil-finite-type-morphism`, which explicitly supplies a finite type affine covering of the preimage of every chosen affine. It uses `def-pc-integral-scheme` only to make both nonempty chart rings domains. Thus the point x and the prescribed U are retained; there is no assumption that the whole morphism is quasi-compact. This is a direct application of the definitions.

Step 2 uses the reduced-and-irreducible characterization in `def-pc-integral-scheme`, the definition of irreducibility in `def-weil-irreducible-components`, the zero-prime generic point in clause (2) of `lem-weil-pbc-spec-domain-stalks-function-field`, and the closure definition in `def-sc-generic-point`. I checked that both rings are domains before invoking clause (2). The density and uniqueness arguments are written out: a nonempty affine is dense, its zero-prime point is then generic globally, and any competing generic point lies in that affine and has prime zero. No separate sobriety theorem or generic-point existence theorem is hidden.

Step 3 uses the actual germ representatives and equality criterion stated by `def-weil-pbc-module-stalk`. Intersecting a neighbourhood with the chosen open gives inverse ring maps on germs, so the open-stalk identifications preserve the chosen germ maps. `def-weil-locally-ringed-space-morphism` states the restriction-compatible sheaf maps and the induced stalk maps; I checked that restricting the morphism sends precisely the same representative to its pullback germ. This is an elementary construction from the two definitions, not an appeal to an unrecorded compatibility theorem.

Step 4 uses clause (2) of `lem-weil-pbc-spec-domain-stalks-function-field` as an R-algebra assertion, not merely an abstract field isomorphism. With Step 3 it gives exactly the global generic germ maps of the statement. In particular its hypotheses hold for both nonzero domain chart rings, and it establishes fields of fractions using all nonzero denominators.

Step 5 uses only continuity, which `def-weil-locally-ringed-space-morphism` includes, and the generic-point closure definition `def-sc-generic-point`. Pulling back a closed set and then using density proves the generic-point image, with uniqueness from Step 2. It does not invoke a definition of dominance as though it were the generic-point theorem: the closure argument is included in full.

Step 6 uses `def-weil-affine-spectrum` for the affine morphism/ring map correspondence. I opened `lem-weil-pbc-spec-map-stalk-localization` and checked both the prime-preimage assertion and the formula for the actual stalk map, including its germ square. Applying it at Q=0 in B is legitimate since B is a domain. Its image prime is zero by Step 5, giving injectivity of the section map. The same node supplies the localization map, and the representative comparison in Step 3 identifies it with the original f at its generic stalk. This addresses the most delicate C4 issue: an arbitrary fraction-field embedding would not suffice.

Step 7 is the explicit elementary field calculation from Steps 4 and 6. It checks the nonzero denominator after both ring maps, proves preservation of the inverse by multiplying, gives the exact displayed quotient formula, and proves uniqueness and injectivity. It invokes no extra node, because these are ring identities and the fractions already obtained.

I checked B--E of delivery-errors.md against these files. Every non-elementary input is an existing cited statement, not a tag used as a substitute for a node; each citation quote is a literal substring of that statement. No new nodes hide a clause, no proof uses a cited node's proof instead of its statement, and the dependencies are exactly the union of step uses. All non-elementary steps are below 2000 characters. Definition/Mathlib citations are permitted generic tools and leave the unit route unchanged. I found no remaining mathematical correction to make after this review.

For small cases I tested a map between field spectra, the identity and a nontrivial localization of an integral affine scheme, and choosing x itself generic. Zero-dimensional fields have the same zero-prime and stalk formulas. Choosing a smaller V never removes the generic point. The empty-source or empty-chart case is excluded by integrality and the selected x; no separatedness of the integral source is used, and intersections of affines are never asserted affine. Removing dominance would fail, for example for the closed-point map Spec(k) to Spec(k[t]), so it is used exactly where needed. These checks support the unchanged hypotheses.

## Unfinished work

None in this stage-1 split. No Lean file was written and no compiler, Lake or build tool was run. Server dry-run validation and direct delivery follow this report.
