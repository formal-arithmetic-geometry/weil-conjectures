Files written:

- `dag/nodes/sec-curve-estimates/lem-weil-pbc-site-extension-by-zero-exact.json` (statement, split; no Mathlib match).
- `dag/nodes/sec-curve-estimates/def-weil-pbc-site-extension-by-zero-presheaf.json` (definition, unsplit; no Mathlib match).
- `citations.json`.

Attachments: none.

WANTED: none.

The item was checked against Stacks Project Modules on Sites, Lemma 03DJ (label `lemma-extension-by-zero-exact`) and Section 03DH. The existing nodes `lem-weil-pbc-site-restriction-adjunction`, `lem-weil-pbc-abelian-presheaves-evaluation-exact`, `lem-weil-pbc-sheafification-exact`, `lem-weil-pbc-abelian-exact-epi-cokernel`, and `lem-weil-pbc-left-adjoint-preserves-colimits` were opened and their statements verified against each use. The one new definition records the sectionwise direct-sum presheaf used by the source. I also searched the whole DAG and blueprint for the tag and the extension-by-zero construction; no duplicate statement was found. Lean source grep found no declaration carrying the target blueprint tag or this theorem.

## Review by H1

I read the target source and verified its hypotheses: a Grothendieck site, an object W, the localized slice topology, and abelian sheaves. Step 1 uses only the new presheaf definition. Step 2 uses the existing evaluation-exactness statement to turn a sheaf monomorphism into sectionwise injective component maps, then uses the direct-sum formula. Step 3 uses the exact-sheafification node for kernel preservation. Step 4 uses the existing abelian cokernel criterion, the existing adjunction statement, and the existing left-adjoint-colimit statement; each cited node explicitly states the fact used. Step 5 uses the abelian short-exact criterion. I tested the construction on W terminal, the zero sheaf, and the identity short exact sequence; it gives the expected identity or zero maps. Mathlib searches were run for both the item and the created definition using LeanFinder, Loogle, grep, and LeanSearch (the two LeanSearch requests were unavailable and recorded as such for the created node); only generic sheaf infrastructure appeared.

## Not duplicates

`def-weil-pbc-site-extension-by-zero-presheaf` vs `def-weil-pbc-extension-by-zero`: the existing node is the scheme/pro-etale module construction, while this node is the arbitrary Grothendieck-site slice construction by direct sums over maps into W.

`def-weil-pbc-site-extension-by-zero-presheaf` vs `lem-weil-pbc-module-extension-by-zero-adjunction`: the existing node states an adjunction for modules on a ringed site, while this node defines the underlying abelian presheaf by a direct sum and does not assert an adjunction.

`def-weil-pbc-site-extension-by-zero-presheaf` vs `lem-weil-pbc-zariski-extension-by-zero-adjunction`: the existing node is restricted to small Zariski sites of schemes, while this node applies to every category and object and only defines the presheaf construction.

`def-weil-pbc-site-extension-by-zero-presheaf` vs `lem-weil-proetale-weakly-etale-localization`: the existing node identifies a particular pro-etale localization, while this node constructs extension by zero for arbitrary slice categories.

`def-weil-pbc-site-extension-by-zero-presheaf` vs `def-pur-localized-ringed-site`: the existing node defines localized ringed sites and restriction, while this node defines the direct-sum presheaf extension and its sheafification.

`def-weil-pbc-site-extension-by-zero-presheaf` vs `lem-weil-pbc-site-restriction-injectives`: the existing node states a combined exactness and adjunction theorem, while this node is the underlying construction used to prove exactness and makes no injective or exactness claim.

`def-weil-pbc-site-extension-by-zero-presheaf` vs `lem-weil-pbc-site-restriction-adjunction`: the existing node states the adjunction abstractly, while this node gives the sectionwise direct-sum definition of the left-adjoint candidate.

`def-weil-pbc-site-extension-by-zero-presheaf` vs `lem-sc-topological-extension-by-zero-stalks`: the existing node concerns stalks of an extension in the topological-space setting, while this node defines the presheaf extension for an arbitrary category and slice object.

What could not be finished: no Lean code is written at stage 1, and the new definition remains an unsplit queue node as required.

## Second reading by H1

- Item statement: checked against Stacks Modules on Sites, Lemma 03DJ (label `lemma-extension-by-zero-exact`), with the ringed-site statement specialized to abelian sheaves; the site, slice topology, and short-exact hypotheses are all present.
- New node `def-weil-pbc-site-extension-by-zero-presheaf`: checked against Section 03DH, Lemma 03DH/03DI construction of the direct-sum presheaf and its sheafification; the sectionwise formula and restriction maps agree, and the topology is now explicitly the ambient topology on `C`.
- Step 1: the additive direct-sum construction is exactly the new definition and is elementary.
- Step 2: checked against the displayed direct-sum map in 03DJ; sectionwise injectivity uses the sheaf-kernel/sectionwise-limit statement and exact evaluation of presheaves, followed by the finite-support direct-sum argument.
- Step 3: checked against 03DJ's exact sheafification sentence; the zero presheaf kernel remains zero after sheafification by the finite-limit clause.
- Step 4: checked against 03DJ's right-exactness argument; the abelian cokernel criterion, the adjunction, and left-adjoint preservation of colimits state each cited fact.
- Step 5: checked against the conclusion of 03DJ; monomorphism plus cokernel gives the short exact sequence by the cited abelian criterion, and the final inference is elementary.
- Small cases: `W` terminal, the zero sheaf, the empty slice, and the identity short exact sequence all give the expected direct sums and zero/identity maps.
- Searches: the new definition's recorded LeanFinder, Loogle, grep, and unavailable LeanSearch queries were checked in `searches.jsonl`; no Mathlib declaration states this construction or exactness theorem.

Changes made: corrected the definition's sheafification topology wording; added the missing sheaf-kernel dependency and citation to Step 2; retained the direct-sum proof route and all existing node distinctions.
