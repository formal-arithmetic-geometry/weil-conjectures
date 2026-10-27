# Stage-1 report: lem-trf-smooth-tower-index-synchronization

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-smooth-tower-index-synchronization.json`: item, statement unchanged, split into eight explicit steps; no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-fine-monoid-local-smooth-charts.json`: one new statement-only lemma, unsplit, no Mathlib match. It supplies ILO's localization lemma and affine neighborhood description, not a clause about resolution towers.
- `citations.json`: one entry for every step/node pair, quoting the cited statement verbatim. Full statements are quoted where the step uses multiple clauses.
- `searches.jsonl` and `item-search-*.txt`: actual msearch logs and retained item search outputs. `ilo.txt` is the local PDF text used for reading. All writes are inside this item's sandbox.

## Attachments

None. Searched `lean/WeilConjectures/` for the exact blueprint id, smooth tower synchronization, Monoscheme, KatoFan, sharpening and saturated blowup. No declaration states this item. The nearby hits about l-adic towers are different objects. No Lean was written or compiled.

## WANTED

None. The ILO PDF is present locally. No SGA source was used.

## What needed repair

The item was a statement-only node created by the preceding sharpening split. There was no earlier sandbox split or report to resume. The statement is correct with its two torsion-freeness hypotheses and its explicit contraction convention, so I kept it verbatim. In particular, contraction requires BOTH a whole ideal and an isomorphism. It is incorrect to discard the first whole-ideal saturation on a nonsaturated monoid, or to discard every principal center.

Read the latest blueprint through `literature/blueprint/latest`, currently commit 7284bb09daf97437d544c51882b325f9c52cd345. Its `lem-trf-local-term-locality` and `sk-i-curve-zero` now use the contracting-correspondence route. This assigned item belongs to the historical monoidal-resolution supporting branch already recorded in its `blueprint.from`. I have not edited the chapter or unit, nor inserted a replacement for their current proof. The original chapter and unit records were also read. The inherited `coord/dag-sync.md` reference is absent; the explicit current brief supplies the read-only live-clone paths used here.

## Source error

ILO VIII 3.1.15, p.100 says that a morphism of monoschemes is smooth if and only if its sharpening is smooth. The reverse direction fails for a general morphism: multiplication by 2 on the group monoid Z is local and its sharpening is the identity of the zero monoid, but the map Z to Z cannot extend to an isomorphism Z direct-sum N^r direct-sum Z^s to Z over its given first-factor map. If r is positive the source has nonunits; otherwise ranks force s=0 and multiplication by 2 is not an isomorphism. Both the ordinary and sharp group completions here are torsion free. Our item's morphism assertion is ONLY the forward direction. Its separate OBJECT smoothness equivalence is valid using the existing unit-splitting lemma. I use precisely these valid assertions; no item statement correction is needed.

## Not duplicates

Searched the whole DAG by ids, monoidal smooth product charts, local homomorphisms, localization, ILO 3.1.14 and 3.1.16; and searched the blueprint index for `monoid`, `smooth monoid`, `local smooth`, `product chart`, `fine monoid`, and `synchronization`. None states the new local chart lemma. Broad localization hits were inspected as candidates only when they concerned these monoids; ordinary ring-localization lemmas do not apply to monoidal-space smoothness.

- lem-trf-fine-monoid-local-smooth-charts vs def-trf-monoscheme-toric-realization: the existing definition defines smoothness on stalks; it does not assert that the smallest neighborhoods are affine stalk spectra or prove localization stability/product charts.
- lem-trf-fine-monoid-local-smooth-charts vs def-trf-fine-fan-blowup: the existing definition gives fine fans, stalk smoothness and fraction charts for blowups; it does not state the local smoothness localization theorem.
- lem-trf-fine-monoid-local-smooth-charts vs lem-trf-monoscheme-finite-chart-components: the existing statement gives finite topology, components and toric realization; it does not give the smallest-neighborhood identification or smooth affine product charts.
- lem-trf-fine-monoid-local-smooth-charts vs lem-trf-sharpening-blowup-chart-comparison: the existing statement compares ideals and blowups under sharpening; it does not give product neighborhoods for an arbitrary smooth map.
- lem-trf-fine-monoid-local-smooth-charts vs lem-trf-smooth-tower-index-synchronization: the new lemma concerns arbitrary fine-monoid localizations and affine neighborhoods, with no tower, rule, contraction, indices or synchronization. The item's tower induction and contraction arguments remain in its proof.
- lem-trf-smooth-tower-index-synchronization vs lem-trf-log-tower-cover-synchronization / lem-trf-log-tower-contraction-descent: those are about strict etale maps of locally Noetherian fs LOG SCHEMES and their scheme-theoretic pullbacks. The item is about smooth monoidal spaces/fans, allowing nonsaturated initial levels and ordinary group factors; neither log-scheme lemma was cited for it.
- lem-trf-smooth-tower-index-synchronization vs lem-trf-descended-resolution-smooth-comparisons: that statement is about ordinary scheme resolution descent and globally labeled centers, not this monoidal-space comparison.

## Arguments retained for the new unsplit node

Read ILO VIII 3.1.4(iii), 3.1.9--3.1.10(ii), 3.1.13--3.1.16, pp.98--100. For a fine monoid P generated by a finite list and a prime p, its complementary face is generated by the members of that list outside p: any expression lying outside an ideal uses only generators outside it. If a is their sum (0 for an empty list), D(a) consists exactly of primes contained in p. This is the smallest open neighborhood and its monoid of sections is the stalk localization. Applying this on a chart proves the claimed canonical affine neighborhood for a point of a monoscheme; with the sharp sheaf it proves the fan version. A continuous map sends generalizations to generalizations, so the map on these neighborhoods is the one on stalk monoids.

For the localization assertion, write Q=P direct-sum N^r direct-sum Z^s. Every localization of a fine monoid is at one element, since an inverted face is generated by the subset of a finite generating list in that face. First localize Q by the elements inverted in P; this leaves the product form with P replaced by P'. Then write the remaining inverted element as (p,n,z). Locality of P' to the final localized Q forces p to be a unit of P': p is a unit in that target because (p,n,z) becomes a unit and all three summands belong to the monoid. Thus only the N^r coordinate matters. Inverting n makes precisely its positive coordinates invertible and gives N^(r-t) direct-sum Z^t; the original group coordinates remain units. This gives the source's Lemma 3.1.14. Passing to sharp quotients removes the group and base units and proves its fan form. A smooth stalk map therefore gives the asserted product presentation of the smallest affine neighborhoods. Conversely, localization stability shows that every local product chart induces smooth maps on every stalk. This argument is source material for the queued child; the new node itself has no proof or proof dependencies.

Mathlib searches were actually made with msearch.py, in all four requested forms, with two distinct semantic phrasings. Read all their returned types and the relevant sources: `GroupTheory/MonoidLocalization/Basic.lean` supplies IsLocalizationMap/LocalizationMap for arbitrary monoids, while `RingTheory/Smooth/Basic.lean`, `RingTheory/RingHom/Smooth.lean` and `AlgebraicGeometry/Morphisms/Smooth.lean` concern rings or schemes. Neither identifies the fine monoidal spectrum/stalk topology or proves this smooth-product assertion. The manifold hits are unrelated. Every tool and query in the child is copied from the actual search log. The item retains its previous recorded searches and appends fresh searches of its own with exact output, including the second phrasing. All these services answered successfully in this run; no unavailable result was called a negative search.

## Review by Q01

I read the actual ILO PDF text at VIII 3.1.13--3.1.26 (pp.100--102) and Remark 2.3.5(i)--(iii) (p.92) for the item, and VIII 3.1.4, 3.1.9--3.1.16 (pp.98--100) for the new lemma. The product-chart and synchronization route follows those passages; the proof is marked agent because the saturated/contraction details are expanded explicitly rather than claimed to be a verbatim source proof.

For Step 1 I opened both definition nodes and `lem-trf-fine-monoid-unit-splitting`. Their statements give the ordinary/sharp smoothness definitions and the isomorphism P = B direct-sum Z^s under exactly the two group torsion-freeness hypotheses assumed here. The quotient calculation proves only the forward assertion for morphisms and both directions for objects, avoiding the source error above.

For Step 2 I read `lem-trf-sharpening-blowup-chart-comparison` in full. Its statement provides the ideal bijection, whole-ideal preservation, corresponding tower levels remaining in C, and all indices; I do not borrow anything from its proof. The separate unit-splitting statement applies at every such level. The chart at the whole ideal's generator 0 shows that the map is saturation, and the closed-stalk/unit calculation establishes its isomorphism criterion. Torsion-freeness of the sharp group ensures that sharpening does not hide new units in its saturation. Thus the conjunction used by the contraction definition is really reflected.

For Step 3 the cited new lemma explicitly supplies local affine product charts, not just the definition of smoothness. I wrote out the two monoid chart equalities, the saturation calculation, overlaps, base case and induction step; I did not cite a definition as if it were a theorem on smooth base change. Every fraction lies in the specified group completion, and the nonnegative coordinate condition is unchanged by multiplying by a positive integer.

For Step 4 the only inputs after Step 3 are the prime-ideal and local-map definitions in the cited definition nodes. The prime p times K proves actual levelwise surjectivity; no nonexistent general base-change theorem is assumed. At a stalk, an ideal containing a unit contains 0, and the local-map condition reflects units. Surjectivity then checks all target stalks. For Step 5 the product saturation calculation from Step 3 and the isomorphism criterion from Step 2 prove the retained-index assertion. The definitions really require a whole ideal AND an isomorphism. These two steps are elementary calculations from earlier steps and the quoted definitions, not independent claims hidden behind the word 'preserved'.

For Step 6 the new lemma states the FAN chart version as well. The sharpened product calculation, prime lift, and local-unit calculation are repeated in this setting. I explicitly checked the torsion-free sharp-group argument for a saturated chart to remain sharp, so the fan isomorphism criterion does not silently use an assertion about ordinary sheaves instead.

For Step 7 I checked that the identity comparison is a hypothesis of the item and that contraction is exactly the one defined in the cited nodes. The finite-length equality forces no deleted stages, including when length is zero. The surjective comparison then follows from Steps 4--5. Step 8 uses only the definitions and the given comparisons: disjoint-union stalks prove membership in C and smoothness, the identity component gives surjectivity, and the explicit composition of comparisons restricts to the full towers. Ideals and indices are preserved before restriction and remain indexed afterwards even if a restricted stage is trivial. Nothing asserts that f and g themselves are equal.

I checked delivery-errors B--E: the child is self-contained and statement-only; both its notions cite their real definitions; the single new node is neither an elementary chart calculation nor a tower clause moved out wholesale; all cited existing statements were opened, and `citations.json` quotes their actual statements; no new node cites the item and the reused comparison/unit-splitting nodes do not depend on it. No proof step is longer than 2000 characters. The item and child have explicit blueprint ancestry/place and no same-as match. No maintainer-owned fields of existing nodes were changed.

Edge cases checked: r=s=0; the zero monoid and pure group Z^s; P=<2,3> inside Z, where a whole-ideal initial saturation adds 1 and MUST be retained; a proper principal ideal (1+N) in N, whose identity blowup MUST still be retained; length-zero towers; successive whole-ideal identity stages; empty spaces; varying ranks on different components; and smooth maps omitting a component, whose restricted identity stages must keep their original indices in Step 8. For the new lemma, localizing N at its generator gives Z (r drops by 1 and s rises by 1), while localizing only a base coordinate retains the same relative factor. None of these require surjectivity except the exact reflection assertions where it is explicitly assumed.

## Unfinished work

The one new node intentionally remains unsplit for the next stage-1 item. No mathematical clause of the assigned item remains open. Delivery will use the required server dry run and push; no local check_dag, review_split, preflight or compiler is run.
