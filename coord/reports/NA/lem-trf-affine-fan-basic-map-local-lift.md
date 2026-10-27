# Worker report

## Files written

- dag/nodes/sec-trace-formula/lem-trf-affine-fan-basic-map-local-lift.json: statement, split into five proof steps; no full Mathlib match.
- citations.json: eight step/node citations, each checked verbatim against the current cited statement.
- searches.jsonl: five actual searches logged by msearch.py; no unavailable service in this run.
- report.md: this report.

No new nodes, and no new Mathlib leaves. The existing basis-extension, set inverse-image adjunction/finite-products, and set inverse-image stalk nodes are Mathlib leaves already in the DAG.

## Attachments

None. Searches of lean/WeilConjectures for the exact blueprint id, affine fan, FineFan, MonoidSpectrum, MonoidalSpace, sharp monoids, and basic-map notions found no declaration giving this assertion. Ringed-space spectrum constructions are about rings, not sharp monoids, and are not attachments.

## WANTED

None. The item source and generic sheaf sources are present locally.

## Findings and changes

The statement is unchanged and is true with its supplied compatible theta maps. The source is ILO VIII 3.1.1--3.1.8, printed pp.98--99 (PDF pages 104--105), especially the proof of 3.1.8: it leaves the sheaf construction as straightforward. I wrote the missing construction using existing generic tools, retaining the original monoidal-geometric route. proof_origin is agent because these details are expanded here.

The latest blueprint was read through literature/blueprint/latest (main-20261023-1620, commit 7284bb09daf97437d544c51882b325f9c52cd345). Its locality node now follows contracting correspondences; this supporting item belongs to the explicitly historical fan/alteration branch recorded by its ancestors. I preserve that ancestry and do not identify this fan lemma with the current local-term theorem. Whole-blueprint searches for monoid spectrum and sheaf morphism basis found no duplicate imported assertion; the locality search confirmed the ancestor. The chapter and unit records were read; this item is not their key statement and no unit fields were changed.

The searches in the imported item are retained as historical material; all five searches added today are actual msearch.py invocations and agree with this sandbox's log. The first semantic phrasing returns ring-spectrum constructions, and the second returns the generic sheaf-on-basis lemmas. That generic result already has the node lem-weil-pbc-sheaf-morphism-on-basis. No duplicate node is created for it. Loogle MonoidalSpace and the whole-Mathlib monoid-spectrum grep return no hits. LeanSearch returns local ring stalk maps and scheme localizations, which do not give the fan assertion.

## Unfinished work

None in the stage-1 split. No Lean code, compiler, Lake or build tool was run. The repository and launcher files were only read; deliver.py performs the authorized delivery itself.

## Not duplicates

No new node pairs: there are no new nodes. The general basis-extension result and both inverse-image tools are cited in place of creating special-purpose replacements.

## Review by NA

I checked the item against ILO VIII 3.1.3--3.1.8 with the source open. In particular, sharpening is quotient by units, monoidal-space morphisms require local stalk homomorphisms, and the universal-property proof factors a monoid map through localization at the prime determined by nonunits. I also read Stacks sheaves.tex labels lemma-extend-off-basis, lemma-restrict-basis-equivalence (009O), lemma-extend-off-basis-structures and lemma-restrict-basis-equivalence-structures (009R), lemma-stalk-pullback (008H), and the cited Mathlib basis extension signatures in Topology/Sheaves/SheafCondition/Sites.lean. There are no new nodes needing additional sources.

Step 1 uses the actual definition of the basic opens and the actual localization-sections identification. Continuity supplies open inverse images; the cover and intersection equalities show the target is a monoid sheaf. Coincident basic opens do not cause an indexing ambiguity because the assumed compatibility applies to both inclusions.

Step 2 uses precisely clause (a) of lem-weil-pbc-sheaf-morphism-on-basis, whose statement allows any coefficient category. Applying it to commutative monoids gives existence, the specified basic-open maps, and uniqueness. Its source is a sheaf, although that lemma only needs a presheaf source. The target was proved to be a sheaf in step 1. No quasi-compactness, finite-cover condition, or assumption on T is inserted.

Step 3 uses clause (a) and finite-product clause (b) of lem-weil-pbc-sets-inverse-image-colimits-finite-products, and the germ-compatible bijection in lem-weil-pbc-sets-inverse-image-stalk. I initially considered the existing ring-valued topological inverse-image node, then rejected it because its statement excludes monoids (C4). The chosen set-valued results do apply. The monoid lift is written explicitly by transporting addition and zero through products; the two addition maps agree because their adjuncts agree. This is a short algebraic-structure argument from the cited statements, not an uncited monoid adjunction theorem. Germ compatibility checks the operation and stalk-map identifications.

Step 4 uses the stated localization germ compatibility, not anything from the proof of that node. For every denominator f in F_x, h(x) lies in D(f), so its fraction is genuinely represented on an allowed open. The theta formula with a=f and n=1 is exactly the required value. All localized elements have this form by the localization definition.

Step 5 uses the final zero-germ criterion of the same node, and the definitions of sharpening and local homomorphism in def-trf-fine-fan-blowup. Since f is inverted, its class is zero. I wrote the small algebra showing a sharpening is sharp rather than citing it as an unstated theorem. The target stalks are sharp by hypothesis. Therefore zero inverse image equals zero, which is exactly locality here.

I tested P={0} (one-point spectrum and trivial source), P=N (generic stalk zero, closed stalk N), P=N^2 at each face, the empty source T, the empty open U, denominator f=0 and numerator p=0, and coincident basic opens. The zero criterion behaves correctly in every case; an all-zero phi maps points to the empty prime and the localized stalk is zero. No integrality of A, cancellation in A, saturation of P, or finiteness of T is used. The only localization is in the fine integral P. Every step is under 2000 characters, and each non-elementary ingredient is cited. B--E checks found no new-node formatting, duplication, clause relabelling, cycle, source-hypothesis, or route-lock problem. No SGA source is used.
