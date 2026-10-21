# Stage-1 report: lem-sfb-locally-prescribed-modules-small

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-locally-prescribed-modules-small.json`: existing statement node, now split into six steps. The statement and statement dependencies are unchanged. Mathlib searches found no exact match or one-line specialization.
- `citations.json`: one exact statement quotation for every step/node citation.
- `report.md`: this report. `searches.jsonl` contains the actual searches; `write_split.py` is sandbox-only preparation code, not a delivery node.

There are **0 new nodes and 0 Mathlib leaves**. Elementary Hom-set counting and code construction remain proof steps. The non-elementary gluing theorem already has a node.

## Attachments

None. Searched the project Lean by the exact blueprint tag/id, prescribed-local-model terminology and essential-smallness terminology. The nearby constructible-module essential-smallness theorem in `WeilConjectures/SixFunctors/ProEtale/ModuleObject/ConstructibleEmbedding.lean` is about the pro-étale site of a Noetherian scheme and constructible modules, not arbitrary prescribed models on an arbitrary small ringed site. It does not attach this item. The existing project declaration `SheafOfModules.existsUnique_hom_of_cover`, in `WeilConjectures/Algebra/Category/ModuleCat/Sheaf/HomCoverGluing.lean`, supports the already existing gluing node; it is not an attachment for this item.

## WANTED

None. All sources used are present in the read-only repository.

## Problems found and changes

The imported item was an unsplit statement without proof, rather than an erroneous statement. Its assumptions suffice, including for sites unrelated to schemes and non-finitely-generated local models. I expanded the blueprint's counting sentence and used only gluing of maps between already existing module sheaves. No effectivity theorem for arbitrary descent data is required.

A tempting shortcut would remove repeated objects from a covering and assert that the resulting family is still a covering. For a site specified by an arbitrary collection of covering families, that assertion need not be part of the axioms. The proof now records only the small object support in the code, chooses one label and trivialization per object, and retains the original covering family when applying gluing. Its repetitions use the same chosen local map. Thus no coverage normalization or extra assumption was introduced.

The universe is not enlarged in the conclusion: the code set and its realized subset belong to the specified universe V. A larger ambient universe only makes the usual representative choice visibly set-indexed. No representative is selected for unrealizable data. The statement is unchanged, so there is no STATEMENT-DISPUTED correction.

## What remains unfinished

Nothing in the requested one-level split. This delivery writes no Lean and runs no compiler. The gluing theorem is reused at its existing node; no deferred theorem or additional node is introduced here.

## Not duplicates

There are no new-node/existing-node pairs because no new node was created. Searching the whole DAG for Tag 04TQ and gluing terminology found `lem-pur-sheaf-hom-cover-gluing`, which states exactly the needed module-map gluing result, so I cite it. `lem-weil-pbc-glue-sheaves-of-modules` is restricted to open covers of a topological space; `lem-amb-etale-sheaf-hom-family-gluing` is restricted to étale schemes. The existing arbitrary-site node avoids creating a duplicate or incorrectly applying either specialization. Whole-blueprint searches for “gluing morphisms”, “small site” and “local models” found no other blueprint statement of this item, so `blueprint.same_as` remains the searched empty list. Its inherited `from.node` and exact place already identify the essentially-small paragraph of `det-brown-hypotheses-small`.

## Mathlib search assessment

Preserved the item's inherited Q67 searches. Ran and read six logged searches for Q60: two differently phrased Lean Finder queries, LeanSearch, Loogle, a targeted grep of `Algebra/Category/ModuleCat/Sheaf`, and a broader grep. All services answered successfully. The first Finder query returns section-smallness and `PresheafOfModules.wellPowered` (small subobjects of a fixed presheaf), not a set of global isomorphism types from fixed local models. The second returns small-site equivalences and sheafification results. LeanSearch's `CategoryTheory.Functor.IsCoverDense.Types.sheafIso` compares two already specified sheaves after restriction; it does not supply a small family of global sheaves. Read the relevant Mathlib dense-subsite declarations, presheaf generator/well-poweredness declaration and object-property smallness interfaces. The finite-presentation hits concern a stronger hypothesis than arbitrary local models. None is this statement or a one-line specialization. Queries are recorded exactly as invoked, including the grep patterns; the log retains their subdirectory and hits.

## Review by Q60

I read the chapter record for `sec-six-functors-basics`, the unit record `sk-lem-brown-hypotheses`, and the current main-20261015 blueprint proof `sk-lem-brown-hypotheses-small.proof.md`. This lemma supplies just its “Essentially small” sentence about fixed-site local models and gluing morphisms; it does not replace the unit's stratification or truncation arguments. For the gluing input I read Stacks `sites.tex`, Tag 04TQ, label `lemma-glue-maps` (statement and sectionwise equalizer proof), and `sites-modules.tex`, Tag 03EM, label `lemma-internal-hom` (the module version and reference back to map gluing). I also read the full statement of every node cited in the six steps and the existing project gluing declaration. No new node has a source to review.

Step 1 uses the size convention, the definition of module sheaves/morphisms, and the localized-site definition. The latter actually gives the slice objects and sectionwise restrictions; the module definition actually specifies linear component maps and naturality. Hence the injection of a Hom set into the written product of function sets follows from those definitions. Smallness uses both small site arrows and small section sets, not merely a locally small ambient category. This counting is elementary and creates no new node.

Step 2 uses the size and localization definitions. Finite limits in the item's hypotheses supply all the chosen products. The restricted B objects are on the same slice over each overlap and have the same restricted ring, so their isomorphism sets are the ones counted in step 1. Power sets, indexed unions and products within a Grothendieck universe make D small. This is a displayed coding construction, not an invocation of an unstated descent theorem. No cocycle or cover condition is needed when merely overcounting possible data.

Step 3 uses the site definition for the original cover and the localization definition for restriction of M. Choosing one occurrence per supported object retains an available label even when different occurrences originally had different labels. The resulting overlap maps have the prescribed source and target. I explicitly retained the original cover rather than assuming it can be thinned; the support lies in the small object set even if the chosen cover is presented with redundant indices.

Step 4 uses the localization and module-morphism definitions. I checked the order of the compositions: g is a_V a_U^{-1} for M and b_V b_U^{-1} for N, so b_V^{-1} a_V equals b_U^{-1} a_U after restriction. This proves equality on every object of the overlap slice, exactly the compatibility that the cited gluing statement in step 5 requires. Taking inverses gives compatibility in the reverse direction. The N trivializations are available on every object in the M cover because the two codes have the same support K; their two enumerations need not coincide.

Step 5 cites `lem-pur-sheaf-hom-cover-gluing` for precisely its stated existence and uniqueness of an O|_U-linear morphism from compatible local linear morphisms, and `def-pur-localized-ringed-site` for C/1 and restrictions. I checked that R is commutative, M and N are global R-modules, all relevant pullbacks exist by finite limits, and the cover is the original cover of 1. Apply the lemma separately to the maps and inverses, then apply its uniqueness to each composite versus the identity. Thus this step derives an isomorphism, not merely a global map. The existing node is declared in `split_report.tool_uses` as a generic off-unit tool. It is not a disguised new node stating the item's conclusion.

Step 6 uses the universe and module definitions for the set of codes and set-coded sheaves. The realized subset S remains in V. Section sets, operations and restriction graphs for one module sheaf have V-small indexing, so the class of such coded sheaves is a set in an ambient universe containing V. Ordinary choice there selects a realization for each s, and steps 3–5 prove that every M has one of those isomorphism types. This closes the argument without assuming effectivity of all data in D or choosing from a proper class.

I tested the statement and proof when all I_U are empty: if no empty cover exists, P and S are empty; if an empty cover of 1 exists, all module sheaves have unique sections on every object and are isomorphic to the zero module. The empty code then has realizations, and uniqueness in the gluing lemma still identifies them. I also checked a singleton identity cover (the result is just the small model family), zero models, repeated objects, and non-monic cover arrows. For the last case U times U is not identified with U; the code retains the entire self-overlap isomorphism. No Noetherian, affine-intersection, finite-presentation or arbitrary-descent hypothesis is used. All steps are under 2000 characters; the sole non-elementary step cites the theorem carrying its actual content. B–E review found no remaining new-node, dependency, quotation, circularity or missing-hypothesis issue.
