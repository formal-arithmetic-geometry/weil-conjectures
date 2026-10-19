# Stage-1 worker report

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-top-degree-open-restriction-surjective.json: existing statement, split into ten steps; fresh Mathlib searches found no match.
- dag/nodes/sec-proper-base-change/lem-weil-pbc-punctured-neighborhood-cohomology-colimit.json: one new statement-only node, unsplit; no Mathlib match.
- citations.json: one verbatim statement quote per cited node per proof step.

There are one new node and zero new Mathlib leaves. Only sandbox files were written directly; no Lean, compiler, Lake, build, live-project modification or push was performed. The authorized delivery dry-run packages and checks the sandbox through its own script.

## Attachments

None. I searched the slopmaster2 project sources by the exact item id and by top-degree, cohomological-dimension, restriction-surjectivity, and neighborhood-cohomology terminology. I also searched the master reference sources by the id and the proposed child's neighborhood terminology. No project declaration stating either entire assertion exactly was found. The curve assertion C8 concerns torsion etale degree-two cohomology, not arbitrary O_X-module Zariski degree-d cohomology, and is not an attachment. The master source was treated only as reference material.

## Wanted sources

None. All sources needed are present locally.

## Corrections and scope

The item's statement is true as written and was preserved. Its empty proof was replaced. I read the chapter record, sk-thm-p1 unit record, and the master Artin--Schreier blueprint node. The ancestor's proper connected calculation needs finite-dimensional H^1(C,O_C); the parent top-coherent-cohomology-finite uses the closure-to-open restriction for that input. This split stays below that auxiliary route and does not alter the chapter or unit. This item is not the unit's statement node, so no realization fields were changed.

The proof of Stacks 0A3G(2) uses vanishing on the generalizations of the boundary with the boundary removed. For the present Noetherian case I reuse the existing general Noetherian vanishing node (02UZ) instead of reproducing the spectral theorem's simultaneous induction. The neighborhood-continuity input is kept as a genuine smaller new lemma (0A3D(2)); the new node does not assert restriction surjectivity or impose a dimension. It has no proof or proof dependencies.

I did not use lem-sc-mayer-vietoris-open-cover, which requires quasi-coherence, nor lem-sc-noetherian-cohomology-above-dimension, which also requires quasi-coherence. The actual cited Mayer--Vietoris node is for arbitrary modules on a ringed space, and the actual vanishing node is for arbitrary abelian sheaves on a Noetherian topological space. Similarly, objectwise module/abelian agreement does not by itself assert compatibility with open restriction. Step 3 supplies that compatibility using an explicit common resolution and the statements providing its acyclicity.

## Not duplicates

No existing DAG node with source Tag 0A3D was found, and no imported blueprint node states the new punctured-neighborhood comparison. Searches included the exact tag, cohomology-of-neighbourhoods, neighborhood cohomology, punctured neighborhoods, and generalizations. The existing spectral-generalizations-of-quasi-compact node states a topological description of W, not any cohomology comparison. Existing continuity nodes for etale limits concern different sites and schemes, and the closed-point/proper-base-change stalk comparisons have different hypotheses. The new node therefore does not duplicate any of them. The whole-blueprint searches '0A3D', 'cohomology of neighbourhoods', 'punctured', 'neighbourhood', and 'top-degree' were inspected; none states the item or new child. The precise ancestor and via path are recorded in both nodes.

## Mathlib search review

All fresh searches ran through msearch.py and are saved verbatim in the node records and search-results.json, with the corresponding searches.jsonl log. Each node was searched with two semantic phrasings, Loogle, source grep, and LeanSearch. LeanSearch returned HTTP Internal Server Error and is recorded as unavailable. I read the returned signatures: section-surjectivity and localization lemmas do not control top-degree cohomology, the Hom-complex quotient-surjectivity result concerns representatives in one complex, skyscraper colimits concern stalks, and the Loogle presheaf-colimit lemmas do not give higher cohomology of a changing underlying space. Grep returned algebraic local-cohomology colimit definitions and unrelated Ext representative arguments, not the new comparison. Neither node is a Mathlib leaf.

## Review by NB

I read cohomology.tex at 0A3G (proposition-cohomological-dimension-spectral), especially the entire proof of part (2), at 0A3D (lemma-cohomology-of-neighbourhoods-of-closed), and at 01F1 (lemma-modules-abelian). For the new child I checked the actual 0A3D(2) statement: E must be quasi-compact and constructible. Closed Z in spectral T is quasi-compact; its quasi-compact open complement makes Z constructible (the complement of a quasi-compact open). Thus the child's hypotheses really imply both source hypotheses. Its colimit is over a set of opens, not an unrestricted large category. T is a neighborhood, and spectral quasi-separatedness makes intersections quasi-compact. I also read the source proof through the punctured-neighborhood limit lemma, rather than mistaking a stalk comparison for this assertion.

For step 1 I opened each of the three cited node statements. The closed-subsets-minimal node supplies exactly Noetherian topology, the locally-Noetherian-quasi-separated node supplies exactly quasi-separatedness, and the qcqs-scheme-spectral node supplies spectrality under these verified hypotheses. I read Properties 01OZ and 01OY. Step 2 uses the finite-discrete conclusion of lem-sc-zero-dim-noetherian-finite-discrete (checked against Properties 0AAX) and the H^0 global-sections definition; gluing with zero proves the restriction assertion directly, including the empty open.

For step 3 I checked 01DI in injectives.tex, 01E1 and 01F1 in cohomology.tex, 03FD in sites-cohomology.tex, and Leray's acyclicity lemma in derived.tex. The four cited statements respectively give enough module injectives, restriction of a module-injective resolution, abelian acyclicity of every injective module on any ringed site object, and computation by a termwise-acyclic resolution. Applying these to the ringed sites of each open B computes both groups with the identical sections complex. The induced restriction chain map is the same on both sides, so the square commutes. No injectivity after forgetting module structure is claimed: acyclicity is what is needed and what the cited node actually gives.

Step 4 proves hereditary Noetherianity and generalization stability explicitly and cites no hidden topology theorem. Step 5 uses only the spectral definition's sobriety and the definition of Krull dimension; I checked the closure formula S intersect closure_T(C)=C for relatively closed C, strictness of each closure inclusion, and the extra bottom member closure{z}. Its strictness follows because Z is closed and excludes the generic point y. This establishes the precise bound d-1, including S empty, without creating a dimension-drop node. Step 6 cites the exact arbitrary-abelian-sheaf Noetherian vanishing statement (02UZ), with nonnegative bound d-1 and degree d strictly greater than it. I opened that node's entire statement; it explicitly covers the empty space.

Step 7 cites only the new child's displayed isomorphism and canonical restriction maps. The source applies with Z closed, U quasi-compact, degree d nonnegative, and A abelian. Step 8 writes the concrete directed-colimit quotient construction; equality of a representative and zero means equality at a common smaller neighborhood. It then uses the already-established restriction square to get the zero restriction in module cohomology. There is no unsupported claim that an objectwise comparison automatically transports the map.

For step 9 I opened lem-sc-mayer-vietoris-ringed-space and checked 01EB. Its arbitrary-module sequence, exactness, restriction map and difference-of-restrictions map are exactly what is used. N contains Z, so U and N do cover X. The pair (xi,0), rather than merely xi, is in the kernel and yields the desired preimage. Step 10 uses the k-scheme structure and the cohomology definition; degreewise module-linearity explicitly gives k-linearity after taking cycles modulo boundaries. It also covers the degree-zero branch.

I tested U empty and U=X, d=0, Z empty, S empty and the generic-to-closed-point chain in dimension one. The continuity child is sensible for Z=T (both sides are zero on the empty puncture) and Z empty (the empty neighborhood forces the colimit to be zero). Degree zero is included in that child. No properness, coherence, quasi-coherence, affineness or separatedness was added. All definition references are to nodes that define the actual notions. I checked B1--B10 (statement-only new node, complete objects and notions, correct tags, literal TeX, honest searches and ancestry), C1--C8 (no unrecorded non-elementary input, every citation supports its exact use, generic tool declarations and no cycle), D1--D5 (the steps carry the lifting argument; nothing is moved into a surjectivity restatement), and E1--E7 (all hypotheses, specialization direction, morphism identity, dimension and scalar formulas). citations.json copies each cited statement verbatim. Generic tools from other units are declared in split_report.tool_uses and preserve the unit route.

## Unfinished work

Only the new 0A3D dependency remains statement-only as required by one-level splitting. Its own proof is future work. The present item's proof is complete relative to the cited statements. A fresh second reader must review and deliver; this worker does not push.

## Second reading by NB

I reopened the item source at Stacks Tag 0A3G, label proposition-cohomological-dimension-spectral, and checked every hypothesis and clause: the field, Noetherian scheme, dimension $d\geq0$, quasi-compact open immersion, arbitrary module sheaf, canonical $k$-linear restriction, and the absence of coherence and properness assumptions all agree.

- Step 1: checked against the statements of the minimal-closed-subset, locally-Noetherian-quasi-separated, and qcqs-spectral nodes and Properties 01OZ, 01OY, and 094L; each cited statement supplies exactly the topological property used.
- Step 2: checked against the finite-discrete node (Tag 0AAX) and the derived-global-sections definition; the degree-zero gluing argument also covers empty and full opens.
- Step 3: checked against Tags 01DI, 01E1, 01F1, and 03FD plus the Leray acyclicity node; the common restricted resolution proves compatibility of module and abelian restriction maps.
- Step 4: checked the Noetherian and generalization arguments directly from the definitions; no unstated quasi-coherence hypothesis is used.
- Step 5: checked the closure chain argument against sobriety and the Krull-dimension definition; the added generic-to-boundary closure is strict, including the empty case.
- Step 6: checked against the arbitrary-abelian-sheaf Noetherian vanishing node (Tag 02UZ); its hypotheses and the bound $d>d-1$ apply to $S$.
- Step 7: checked against the new Tag 0A3D comparison node; the spectral, closed, and quasi-compact-complement hypotheses and all restriction maps match.
- Step 8: checked the filtered-colimit equivalence relation from the colimit definition; the common-neighborhood restriction is then transported through Step 3's compatible isomorphisms.
- Step 9: checked against the arbitrary-module Mayer--Vietoris node (Tag 01EB); $U$ and $N$ cover and $(\xi,0)$ lies in the kernel exactly as stated.
- Step 10: checked against the scheme-over-base and cohomology definitions; degreewise scalar linearity gives the asserted $k$-linearity, including degree zero.

- New node `lem-weil-pbc-punctured-neighborhood-cohomology-colimit`: reread Tag 0A3D(2), verified the spectral space, closed $Z$, quasi-compact open complement, constructible/quasi-compact input, directed quasi-compact-neighborhood index, restriction maps, and all edge cases; statement-only form, TeX, definition dependencies, source label, blueprint ancestry, and recorded searches are correct.

Changes: added explicit definition citations for identifying the open immersion with its image (step 1), exactness of the module-forgetful functor and the enough-injectives hypothesis for abelian cohomology (step 3), and semilinearity of section restrictions (step 10); step 3 now derives exactness from the cited sectionwise-kernel and sheafified-cokernel descriptions rather than leaving it implicit. Regenerated citations.json with verbatim statements for all citations. Added independent LeanFinder, Loogle, and source-grep searches for the new continuity node, with their literal outputs: only sections/germs, locally constant presheaves, and a Tate-complex finite-colimit result were returned, none an applicable declaration. The node therefore remains genuinely smaller and unsplit, not a Mathlib leaf.

Independent duplicate searches covered the whole DAG and imported blueprint for Tag 0A3D and neighbourhood terminology. The keyword hit lem-fin-boundary-sheaf concerns constructibility of an etale boundary sheaf, not this higher-cohomology colimit, and does not duplicate the new node. Read-only searches of slopmaster2 and upstream master found no exact declaration for either assertion; upstream sorry declarations were not treated as proofs. No source, Lean, compiler, or live-project files were modified.

Validation: the repaired split passed deliver.py --no-push with OK at d5c7171c31. The installed delivery tool accepts no trailing directory argument; its documented two positional arguments were used.
