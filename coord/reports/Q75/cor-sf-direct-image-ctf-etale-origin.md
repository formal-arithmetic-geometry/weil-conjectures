# Q75 stage-1 delivery: cor-sf-direct-image-ctf-etale-origin

## Files written

- dag/nodes/sec-six-functors/cor-sf-direct-image-ctf-etale-origin.json: statement, split into four proof steps; no Mathlib match for the item.
- citations.json: eight literal statement excerpts, one per step/node citation.
- report.md: this report. searches.jsonl is the search command's original log.

No new DAG nodes and no new Mathlib leaves. Existing nodes suffice. No Lean was written or compiled; no repository or launcher file was changed.

## Attachments

None. The previous rejected attachment is not resubmitted. I searched the supplied project source by item id and notion and read the currently supplied file lean/WeilConjectures/SixFunctors/ProEtale/FiniteCoefficient/Derived/Stability.lean. Contrary to the older rejection's path, the file now sits under FiniteCoefficient/Derived; its tagged declaration AlgebraicGeometry.ProEtale.boundedConstructible_and_torAmplitudeIn_rightDerivedLowerStar_mapDerivedCategory begins at line 181 and has an explicit assembly proof. This is source material only: the brief specifically requires a split rather than another ATTACH, and I have no new closure certification of all its dependencies. The mathematical split does not rely on it being proved.

## WANTED

None. All documents used for this split were available locally.

## Corrections and source comparison

The latest blueprint is the snapshot main-20261023-1620, commit 7284bb09daf97437d544c51882b325f9c52cd345 as recorded in literature/blueprint/COMMITS.txt. I read the current statement and separate proof in literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-cor-sf-direct-image-ctf/cor-sf-direct-image-ctf-etale-origin{,.proof}.md, rather than an old snapshot. The live item remains filed under sec-six-functors: I retained its chapter and unit. The statement follows the current blueprint's finite coefficient **ring** wording. The first full dry run rejected the inherited “In the setting of” opening under B2. I therefore expanded all its geometric, field and coefficient hypotheses from cor-sf-direct-image-ctf-nonproper and supplied the defining references, without changing the mathematical hypotheses or conclusion. The final context-dependent reference to summary clause (iii) is expressed self-containedly as membership in D^b_ctf(Y,A). I read the statement of every added definition dependency, including the finite-field datum, coefficient extension, dimension, schemes, étale derived/constructible categories and site conventions.

The blueprint proof's phrase “finite type, hence quasi-compact and quasi-separated” suppresses a hypothesis: quasi-separatedness follows here from the assumed separatedness. Step 1 now cites the existing Mathlib leaf lem-pc-separated-quasi-separated, while quasi-compactness is part of def-weil-finite-type-morphism. The source for the latter is Stacks morphisms.tex, definition-finite-type, Tag 01T1 (in Section 01T0); for the former it is schemes.tex, the paragraph after definition-separated, Tag 01KK, using closed-immersion quasi-compactness, Tag 01K7. I read those paragraphs, as well as the recorded Mathlib separated-to-quasi-separated instance in Morphisms/Separated.lean. No new lemma is needed.

The blueprint's bounded-constructibility citation lem-weil-pbc-pullback-preserves-bounded-constructible states preservation along a morphism of schemes, not along the comparison of sites. It therefore cannot justify this use. Step 3 instead gives the actual defining witness (L,e) required by def-weil-pbc-proetale-modules. This is the elementary defining-membership part of a step whose non-elementary comparison is explicitly cited. The stalk-conservativity lemma is unnecessary and removed from the proof dependencies: no geometric-stalk conservativity on arbitrary pro-étale sheaves is assumed.

I read the recorded unit and chapter. The imported unit describes exactly the comparison route realized here. The latest blueprint reorganizes its sketch as an open-immersion theorem, but leaves this general finite-type étale-origin corollary and its proof intact. This item is not the key node of that unit, so no unit realization is edited. The server review notes the existing empty unit realization; this delivery does not claim to fill it.

## Searches and duplicate audit

I ran the required msearch.py command for all six queries recorded in the item's mathlib_searches and read their returned hits. Both semantic phrasings give topology/cohomological-bound primitives or structure-sheaf pushforwards and constructible subsets, not constructible module-sheaf derived direct images with a Tor interval. The first grep has no hits; the broader grep finds the pro-étale topology and ell-adic-cohomology definitions. I read Mathlib/AlgebraicGeometry/Sites/Proetale.lean; these topology declarations do not prove the item. The Loogle hit for separated implies quasi-separated is reused through the already existing leaf, not misclassified as an item match. All services answered; none was recorded as unavailable or fabricated.

I searched the whole DAG and tools/blueprint_refs.py by “direct image”, “quasi-separated” and “étale origin”. The exact item and its existing inputs were found; none of the other returned statements is an alternative statement of this precise étale-origin corollary. Hence blueprint.same_as is []. No new node is proposed, so there are no new/existing same-tag pairs requiring distinctions.

## Not duplicates

No new nodes; no pairs.

## Review by Q75

I checked the split against delivery-errors B–E with the current item, the eight cited node statements and the current blueprint open. I read the current nonproper corollary and its proof, the comparison-direct-image statement and proof, and the Tor-comparison statement and proof. I also read Stacks proetale.tex Section comparison (099R), lemma-compare-constructible (09AK) and lemma-compare-constructible-derived (09AL). Those support the comparison setting and constructible categories; I do not pretend that 099R itself is the whole derived direct-image theorem. That theorem is supplied by the existing cited node. No SGA route is used.

For step 1 I verified that def-weil-finite-type-morphism explicitly includes quasi-compactness, and lem-pc-separated-quasi-separated explicitly concludes that the diagonal is quasi-compact for a separated morphism. Its separatedness hypothesis is present in the setting inherited from cor-sf-direct-image-ctf-nonproper. Bounded implies bounded below directly. This repairs the missing reason for quasi-separatedness without adding a hypothesis.

For step 2 I compared cor-sf-direct-image-ctf-nonproper clause by clause: the same finite ring A_{E,n}, prime distinct from the characteristic, algebraically closed finite-field base, finite-type source and target, separated finite-type f, source dimension at most d, and the bounded constructible étale input with interval [a,b] are all available. Its conclusion explicitly supplies both bounded constructibility and [a,b+2d], not merely a cohomological bound. Thus the newly named L is also bounded below, as required in step 4. I have not substituted a proper-map statement or a general finite ring for the specified coefficient stage.

For step 3 the statement of prop-weil-pbc-comparison-direct-image supplies exactly nu_Y^* Rf_et,* K' ≅ Rf_proet,* nu_X^* K' for qcqs f and bounded-below K'. Step 1 verifies those hypotheses. Applying a functor to the given isomorphism and composing isomorphisms is elementary category theory. The resulting e has the direction nu_Y^*L ≅ Rf_*K; def-weil-pbc-proetale-modules explicitly defines bounded constructibility by just such a witness with L bounded constructible. No scheme-pullback lemma or statement about geometric stalks is used. The comparison proposition is declared as a generic tool use, since it is filed under proper base change while imposing no properness hypothesis.

For step 4 I checked that lem-exc-comparison-tor-interval is stated for an arbitrary scheme and a finite commutative ring, and for bounded-below input; all apply to Y,A,L. Its conclusion tests *every* module sheaf on the full small pro-étale site, including ones not of étale origin. I read def-weil-proetale-tor-amplitude and the finite-stage clause of def-weil-finite-tor-amplitude: the required condition is exactly the cohomology vanishing for those arbitrary tests. The proof spells out tensoring e and applying cohomology so that invariance under the derived isomorphism has an explicit argument. This invokes the functoriality already built into derived tensor, not an extra projection formula or a hidden Tor comparison.

I tested the zero complex and the empty source, for which every claimed vanishing is immediate; d=0 and a=b, for which the interval stays unchanged when d=0 and the comparison does not create a shift; f=id, for which the isomorphism is the identity comparison; and a proper f as a compatible special case that is not used in the proof. As in def-weil-proetale-tor-amplitude, Tor intervals are ordered intervals a≤b; d≥0 ensures a≤b+2d. There is no claim that bounded constructibility alone implies finite Tor amplitude, nor that testing geometric points suffices on the full pro-étale site.

Every used non-elementary assertion is a cited node's statement. The eight excerpts in citations.json were checked as literal substrings of those statements; proof_deps is exactly the union of uses. No step is longer than 2000 characters. There are no new-node definition, source, hidden-proof, Mathlib-leaf or duplicate obligations left unfilled. The initial server review_split check returned PASS with zero new nodes and the comparison tool use declared. The full preflight then found the inherited B2 context problem; the expanded statement repairs that failure. No mathematical statement dispute or weakened conclusion is involved.

## Unfinished work

None at stage 1. The cited inputs retain their own independent formalization obligations. Full delivery dry run and push are performed after this report is written.
