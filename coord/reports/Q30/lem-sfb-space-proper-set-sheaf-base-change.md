# Stage-1 worker report: Q30

## Files written
- dag/nodes/sec-six-functors-basics/lem-sfb-space-proper-set-sheaf-base-change.json: statement item split in six proof steps; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-scheme-proper-set-sheaf-base-change.json: new statement-only input, Stacks 0A3U; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-space-proper-surjection-set-sheaf-equalizer.json: new statement-only input, Stacks 0DFX; no Mathlib match.
- citations.json: exact statement quotations for each cited node in every numbered proof step.

## Attachments
None. Searched the project WeilConjectures tree for the item tag and the concepts. Read Etale.isIso_baseChangeMap_of_isProper in UnderivedExchange.lean, lines 144ff: it has module coefficients, not arbitrary sheaves of sets, and schemes rather than algebraic spaces. The existing DAG proper-underived-exchange statement is even restricted to torsion. No attachment is claimed.

## WANTED
None. All mathematical sources used are in the local Stacks source tree. No SGA source was used.

## Corrections and scope
The imported statement is correct and unchanged, including arbitrary nonrepresentable proper f, arbitrary g, arbitrary set sheaves, and the canonical counit mate. The source 0DG0 ends with details omitted: the equalizer comparison, its arrows, and the identification with the specified mate are written out in steps 4-6. Neither new node is the algebraic-space base-change assertion restated: the first only treats schemes; the second treats descent of a sheaf pulled back along a proper surjection, with no arbitrary base-change morphism.

Read the chapter/unit records and the latest blueprint at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/: _section.md, the direct-images statement, and its proof. This remains a supporting sheaf-theoretic tool in the inherited direct-images/moduli route. No chapter or unit route is changed. The inherited node has a null blueprint ancestor; blueprint_refs.py ancestor reports that fact. Retained the existing null anchor and via chain and added precise Stacks proof places for the new inputs, as the reviewed parent already does; did not invent an anchor.

A minor source proof typo is recorded for the future splitter of 0DFX: after saying the assertion is etale local on X, the printed proof says assume Y affine. It must say X affine, since the following lines apply weak Chow to Y and call Z -> X a morphism of schemes. This does not affect the theorem's statement. For the new scheme 0A3U node, the source omits compatibility with the canonical map; a future splitter must check the stalk representatives against the counit mate. No proof or proof dependency is written inside either new statement-only node.

## Search record
Ran five searches per subject with the prescribed msearch.py command, all successfully available: LeanFinder twice with distinct phrasings, Loogle, Mathlib grep, and LeanSearch. Kept the original item's six search records and appended the five Q30 runs. Every new-node entry is copied from the actual searches.jsonl record; search-*.txt preserves every returned hit. The proper/base-change hits are scheme morphism-property stability; the adjunction/composition hits are structure-sheaf module or ordinary sheaf functor formulas. The equalizer hits are abstract sheaf conditions, fpqc morphism-property descent, and coherent/condensed sites, with no proper-surjection input for small etale set sheaves. None specializes to a new node. Searches of the whole DAG by tag and concept and blueprint_refs.py searches for proper base change, proper surjective, weak Chow, equalizer, and sheaves of sets produced no matching blueprint node. Reused weak Chow 089J and properness permanence rather than creating copies.

## Review by Q30
I read spaces-more-cohomology.tex 0DG0 and its proof in full for the item, etale-cohomology.tex 0A3U and its proof for the scheme input, and spaces-more-cohomology.tex 0DFX and its proof for the proper-surjection equalizer. I also read spaces-cohomology.tex 089J and its proper scheme-cover statement, checking that separated finite type over an affine scheme suffices and that finite presentation is not imposed.

Step 1 uses exactly the enlarged-site localization/composition assertion of lem-trf-space-enlarged-etale-ringed-site-model, the fibre-product direct-image formula of lem-trf-space-enlarged-chart-ringed-morphism, the atlas clause of def-trf-algebraic-space, and the covering stability clause of lem-trf-space-fibre-products-etale-covers. Restriction makes the two functors literally the ones for the chart square. Sheaf gluing proves the local inverse criterion explicitly, so arbitrary g is not silently assumed etale. Only these localizations are used to reach affine base schemes. The proper-base-change node is also cited explicitly to retain properness of each restricted vertical map.

Step 2 uses the full statement of existing lem-sfb-space-weak-chow for a proper universally surjective scheme cover, not its proof. Proper f supplies separated finite type over affine Z. The representable diagonal in def-trf-algebraic-space makes the double overlap a scheme: it is a pullback along Y_1 x_S Y_1, which is a scheme because S is a scheme. I corrected an unnecessary absolute-diagonal description during self-review to this relative S description. Proper base change and proper composition are exactly the statements of the two named sfb nodes, and give proper k_1 and k_2 without finite-presentation assumptions. Forgetting to Spec Z for the existing weak Chow node preserves the objects and morphisms involved.

Step 3 uses only the universal property from the fibre-product node for the cartesian identifications; proper base change makes h_1' proper; the explicit universal-surjectivity clause of weak Chow makes h_1' surjective. These are the hypotheses of the new 0DFX node on both sides. Its statement gives precisely the two sheaf equalizers with projection-unit arrows. The old trf equalizer cannot replace it, because that node is only global sections of abelian sheaves on schemes.

Step 4 uses the sectionwise-limit statement of lem-weil-pbc-site-sheaf-sets-limits-sectionwise and the actual left-exact-inverse-image/direct-image-evaluation clauses of the chart morphism node; it does not cite a definition as an exactness theorem. The diagrams are finite and hence small in the stated universes. The new 0A3U scheme input applies to the proper scheme maps k_i and the arbitrary map g between the affine schemes obtained in step 1. Its canonical mate is the b_i used here. All coefficients remain sets.

Step 5 checks the actual arrows, not just abstract isomorphisms: projection arrows are the displayed adjunction units; expand the units and counits of composites, apply their naturality, and cancel the adjacent unit/counit by the triangle identity. The two cited site nodes supply the canonical adjunctions and composition comparisons; the rest is this elementary adjunction calculation. The same composite-counit formula checks that the induced equalizer map is the beta named in the item's statement.

Step 6 uses only sectionwise equalizers and the naturality of the same comparisons: b_1 and its inverse preserve matching because b_2 is invertible. This proves the specified map is invertible and natural. I checked both new statements on empty spaces, identity maps, and disconnected spaces; the equalizer also covers nonreduced proper fibres. Empty set sheaves cause no issue: the proofs use matching sections and adjunctions, without choosing a section or requiring a group zero. No torsion, finite presentation, representability of f, or surjectivity of f is used. Only the auxiliary weak Chow map is required to be surjective.

I checked delivery-errors B-E against these files: self-contained notions and exact tags; no proof in a new unsplit node; every non-elementary fact cited as a statement; no use of another node's proof; no clause hidden in a new node; and no missing geometric hypothesis. All six steps have fewer than 2000 characters. The off-unit trf tools are general site/space foundations and are declared in split_report.tool_uses. No top-level tool_uses or reviewed record was written.

## Not duplicates
lem-sfb-scheme-proper-set-sheaf-base-change vs lem-sfb-space-proper-set-sheaf-base-change: the new node is only the scheme case used after weak Chow; the item treats arbitrary algebraic spaces and is proved by localization and two equalizer diagrams.

lem-sfb-scheme-proper-set-sheaf-base-change vs lem-weil-pbc-strict-local-section-pullback: the existing node is a representative compatibility formula for module-sheaf strict-local sections, not arbitrary set-sheaf proper exchange.

lem-sfb-scheme-proper-set-sheaf-base-change vs lem-weil-pbc-qcqs-strict-local-module-comparison: the existing node is a module-sheaf stalk-to-strict-local-section continuity assertion, not arbitrary set-sheaf proper exchange.

lem-sfb-scheme-proper-set-sheaf-base-change vs lemma-weil-pbc-proper-underived-exchange: the existing statement is torsion etale module/abelian sheaves on schemes; the new node permits arbitrary set sheaves with no group or torsion structure.

lem-sfb-scheme-proper-set-sheaf-base-change vs lem-weil-pbc-strict-local-exchange-compatibility: the existing node is a module-sheaf geometric-stalk factorization conditional on a comparison map, not arbitrary set-sheaf proper exchange.

lem-sfb-scheme-proper-set-sheaf-base-change vs lem-weil-pbc-exchange-pointed-representative: the existing node is a module-sheaf pointed representative identity, not invertibility for arbitrary set sheaves.

lem-sfb-scheme-proper-set-sheaf-base-change vs lem-weil-pbc-proper-geometric-point-exchange: the existing node treats module coefficients and a geometric-point base change; the new node treats arbitrary set sheaves and arbitrary scheme base change.

lem-sfb-scheme-proper-set-sheaf-base-change vs lem-weil-pbc-qcqs-geometric-exchange-factorization: the existing node factors a module-sheaf geometric-point exchange through strict localization, without asserting the middle restriction invertible; the new node asserts set-sheaf proper exchange for arbitrary scheme base change.

lem-sfb-space-proper-surjection-set-sheaf-equalizer vs lem-trf-proper-surjection-etale-section-equalizer: the new node applies to arbitrary algebraic spaces and set sheaves and gives the sheaf equalizer; the existing node only gives global sections of abelian sheaves on schemes.

## Unfinished work
None within this one-level split. The two new inputs deliberately remain statement-only for later workers.
