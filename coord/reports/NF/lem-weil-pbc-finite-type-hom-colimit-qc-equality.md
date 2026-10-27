# Stage-1 delivery: lem-weil-pbc-finite-type-hom-colimit-qc-equality

## Files written

- dag/nodes/sec-proper-base-change/lem-weil-pbc-finite-type-hom-colimit-qc-equality.json: statement, split into five steps using existing nodes only; Mathlib verdict no match.
- citations.json: eight verbatim statement excerpts, one for each step/node citation.
- searches.jsonl: actual search-command records, retained without alteration.

New nodes: 0. Mathlib leaves created: 0. The item statement, statement dependencies, imported metadata and blueprint ancestry are unchanged. Existing historical searches are retained, with six searches run for this delivery appended.

## Attachments

None. Searched lean/WeilConjectures for the item id, the exact blueprint tag, finite type/colimit combinations, IsFiniteType, and eventual equality. The finite-type local coefficient and internal-Hom-germ declarations concern other conclusions; no declaration states the item. No compiler or Lake command was run.

## WANTED

None. The relevant Stacks source files and current blueprint are available locally.

## What needed repair

The imported item had no proof. Its finite-type assertion is correct, including its deliberate absence of finite presentation, quasi-separatedness and injective transitions. The injectivity assertion for sections in Tag 009F alone cannot be applied on arbitrary generating neighbourhoods: those need not be quasi-compact. Steps 1 and 2 instead use sheafification local equality, then the eventual-equality criterion for sets, before compactness is used in step 5.

A sheaf epimorphism need not be surjective on sections. Step 4 explicitly forgets to abelian sheaves using the exact forgetful functor, invokes the general-site local-surjectivity result, and writes the local linear combinations and the sheaf uniqueness argument. It never assumes a restricted epimorphism is sectionwise surjective.

The blueprint ancestor's current main-20261015 text is in sk-lem-pbc-p1-injective-fibre, whereas this tool node inherits the historical sk-thm-p1 metadata. I read the current ancestor and its blueprint_update; the existing descent-tool via chain and the item's chapter/unit metadata are preserved. The tool supports the constructible finite-data and finite-presentation descent work behind the finite-pushforward representation; it does not replace a unit-level route.

## Unfinished work

None for this split. The dependency nodes remain separate project tasks; no new unsplit task was necessary.

## Not duplicates

No new nodes. Existing nodes for module colimits, sheafification, local equality, filtered sets and local-surjective epimorphisms are reused. Whole-DAG searches covered Tag 009F, Tag 01BS, local colimit representatives, module colimits and finite-type equality. Blueprint searches for colimit, finite type, eventual equality and finite-type module did not find this assertion elsewhere: the returned Nagata eventual-equality statements concern morphisms or opens of inverse limits of schemes, and the coefficient truncation result concerns a different coefficient construction.

## Review by NF

I read Stacks sheaves.tex Tag 009F (lemma-directed-colimits-sections), especially the proof of (2), and modules.tex Tag 01BS (lemma-finite-presentation-quasi-compact-colimit). The latter's full Hom-colimit bijection assumes finite presentation and a finite-cover condition on overlaps; I do not claim its surjectivity here. The finite-generator version of the equality argument is written as an agent adaptation of 009F, with finite type read from modules.tex Tag 01B5 (definition-finite-type).

For step 1 I opened the statements of lem-weil-pbc-module-directed-colimit-underlying-sets and lem-weil-pbc-sheaves-colimit-sheafification. The first concerns arbitrary ringed topological spaces, precisely these directed module systems, and the specified cocone legs; the second says the sectionwise presheaf colimit sheafifies to the sheaf colimit. I checked sheaves.tex Section 009E (section-limits-sheaves), (3), and modules.tex Tag 01AH (lemma-limits-colimits), (2). The cited colimit definition gives the unique isomorphism, and the proof spells out why it respects the actual legs. The index is a preordered set, hence a small category after choosing a containing universe; nonempty directedness makes it filtered. There is no large arbitrary index category introduced in the proof.

For step 2 I opened lem-weil-pbc-site-sheafification-sections-local and used its explicit final sentence about equal images becoming equal on a covering; it is more than the bare sheafification definition. I read sites.tex Tags 00WB (theorem-plus) and 00WK (lemma-sections-sheafification) and the filtered-sets description in categories.tex Tag 04AX (section-directed-colimits). The statement of lem-weil-pbc-filtered-colimit-sets-elementwise gives exactly the common target and equality of transported representatives. On the opens site a covering gives a neighbourhood of the specified point. All index bounds refer to the same directed preorder and restrictions commute with the maps. No compactness or quasi-separatedness enters this step.

For step 3 I read the complete finite-type definition node. It explicitly supplies finitely many sections and an epimorphism from the finite free sheaf, as well as the correspondence with its basis sections. The hypothesis on the composites gives equality of the images of each generator over the original neighbourhood. The finite intersection and common-upper-bound operations are written explicitly. This step is elementary assembly of step 2 and the definition; it creates no separate finite-list lemma.

For step 4 I opened lem-weil-pbc-module-sheaves-colimits-forgetful and lem-weil-pbc-site-abelian-sheaf-epi-locally-surjective. Their statements respectively give preservation of cokernels and local surjectivity on an arbitrary site, so both apply to the opens site of V_x with ring sheaf O restricted there. I read sites-modules.tex Tag 03DA (lemma-abelian) and Tag 03CN (lemma-abelian-abelian), (5). Preservation of a zero cokernel carries an epimorphism to an abelian-sheaf epimorphism. I then checked the linear combination calculation on an arbitrary smaller open and the uniqueness of sheaf gluing, rather than inferring global sections surjectivity. A finite free module has finite tuples as its sections (equivalently finite products of O), so the displayed sum computes the given free map. Every non-elementary ingredient in this step is covered by its two cited statements.

Step 5 is the finite-cover argument of 009F (2), written on arbitrary test opens and sections so that it proves equality of morphisms. Only U needs quasi-compactness. The common bound includes i and j explicitly; the empty-open case uses nonemptiness and directedness to choose such a bound, and sheaves have a unique section on the empty open. If a generating family is empty, step 3 chooses any common bound, and the empty-sum calculation in step 4 applies. Identity transitions, non-injective transitions and a singleton directed index present no exceptional case. Finite presentation and compact intersections are never used.

I checked delivery-errors B through E against the actual files: no new definitions or nodes to duplicate, self-contained unchanged statement, exact source labels and tags, all proof citations read as statements (not extracted from their proofs), eight verbatim quotes checked, proof_deps exactly the union of uses, no circular use of the item or its parent, and no clause moved into a new node. Every step is below 2000 characters. The two elementary steps are finite-family selection and a finite-cover/sheaf uniqueness argument, with the arguments written out. No source error or statement dispute was found.

The six new Mathlib searches were run through msearch.py and recorded as returned. LeanFinder's scheme inverse-limit and algebraic direct-limit results do not have this sheaf statement. Loogle returned IsFiniteType and its constructors, and LeanSearch returned colimit existence and presentation results. The second LeanFinder phrasing returned definitions and local sheafification facts. The grep hits in Generators.lean:44,95,137,142 concern finite generators; I read these definitions. I also read CategoryTheory/Presentable/Finite.lean:51 and Basic.lean:294: categorical IsFinitelyPresentable implies eventual equality but is a stronger, unavailable hypothesis than locally finite type here. Thus none is an exact match or a one-line specialization for the item. No unsuccessful service call was recorded as a no-match result.

## Dry-run repairs

The first dry run rejected only the short colimit-uniqueness quote (under 40 characters). I replaced it with the complete sentence fragment including the following clause, still verbatim. The generic exact module forgetful functor belongs to sk-thm-reduction; its use is declared in split_report.tool_uses because step 4 needs its module-to-abelian transfer, not a replacement of a unit proof.
