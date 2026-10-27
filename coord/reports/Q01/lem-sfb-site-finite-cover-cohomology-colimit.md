## Worker report

Files written:
- dag/nodes/sec-six-functors-basics/lem-sfb-site-finite-cover-cohomology-colimit.json: item split in four steps; statement and statement dependencies unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-site-quasi-compact-section-colimit.json: one new statement-only node, unsplit, no Mathlib match. It records the objectwise sections criterion 0738(2),(4), with quasi-compactness defined inline.
- citations.json: twelve verbatim statement quotations, covering every uses entry in the item's four steps.

Attachments: none. Searches in lean/WeilConjectures by the item tag, finite-cover/cohomology/colimit concepts, and the general-site CohomologyFilteredColimit module found no declaration with the exact statement. CategoryTheory.Sheaf.H_map_isColimit_of_isFiltered_small in WeilConjectures/CategoryTheory/Sites/CohomologyFilteredColimit.lean:513 concerns a terminal object and assumes finite products in every slice; applying it to arbitrary object cohomology would require an additional slice comparison and additional finite-limit hypotheses. It is not an exact attachment for the present precoverage site.

WANTED: none. The Stacks sources used are present.

The item was unsplit and mathematically correct. Its full statement agrees with sites-cohomology.tex, Tag 0739, lemma-colim-works-over-collection. The parent already clarified that a nonempty iterated product means one or more factors, not a nonempty space. No statement correction or dispute is needed. No earlier split/report was present; earlier searches in searches.jsonl were read and retained, and the more precise sections searches were added. The existing item Mathlib searches are preserved.

The inherited blueprint.from.node is null: tools/blueprint_refs.py ancestor lem-sfb-site-finite-cover-cohomology-colimit prints None because the created.item chain has no resolvable imported endpoint. I preserved that computed value in the item and new node and retained the full via chain. The precise source place is filled. I read latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md, proof (3). This is an existing prerequisite below the direct-image branch, through the algebraic-space cohomology input 073E; no chapter or unit route has been changed and no realization field is owned by this item.

Nothing remains unfinished at the requested splitting level. The new sections criterion deliberately remains unsplit; it is neither a proof sketch nor the whole cohomology assertion renamed.

## Sources and searches

Item: literature/stacks-project/sites-cohomology.tex, Tag 0739, label lemma-colim-works-over-collection, statement and whole proof, lines 2505-2627.
New node: literature/stacks-project/sites.tex, Tag 0738, label lemma-directed-colimits-sections, statement and proof (2),(4), lines 3422-3524; definition-quasi-compact, lines 3252-3264. I also read literature/stacks-project/sites-modules.tex, label lemma-limits-colimits-abelian-sheaves, the sheafification/colimit/exactness clauses used for abelian coefficients.
Other source checks: sites-cohomology.tex, 03AW lemma-injective-trivial-cech, lines 1333-1356; 03F9 lemma-cech-vanish-collection, lines 1564-1645; injectives.tex, 01DP theorem-sheaves-injectives, lines 841-859. The functorial-injective construction is already part of the existing successor node; no duplicate of it is added.

Before creating the new node I searched the whole DAG for 0738 and the sections/finite-cover/quasi-compact/injective concepts, and ran blueprint_refs.py searches for finite covering, functorial injective, 0738, 0739, quasi-compact, quasi-compact object, sections of a filtered, filtered colimit sections, and quasi compact overlaps. There is no blueprint node stating the new objectwise arbitrary-site criterion. Existing topology-only or globally finite-precoverage statements do not cover an arbitrary site with a cofinal family only at the given object.

Every new-node search in mathlib_searches is an actual msearch.py call present in searches.jsonl, with the original query spelling. Two semantic phrasings and LeanSearch, Loogle, and Mathlib grep were read. The closest hit is CategoryTheory.isSheaf_pointwiseColimit, Mathlib/CategoryTheory/Sites/Coherent/ExtensiveColimits.lean:37: it assumes a finitary extensive category and its extensive topology, which are absent here. Sheaf.hasFilteredColimitsOfSize only gives existence, and the point-fiber results concern stalks. No service failure is recorded as absence. Mathlib's generic Grothendieck sheaf theorem was found and inspected at GrothendieckAxioms/Sheaf.lean:72-85 and Grp/AB.lean:109; instead of adding it I reused the existing module-valued leaf lem-cbc-sieve-module-sheaves-grothendieck at integers, with the explicit sectionwise identification in step 4.

## Review by Q01

I read the item against Tag 0739 hypothesis by hypothesis. The site and filtered category are small, the selected covers have finite index sets, target and every iterated overlap belong to the designated collection, and those covers refine every covering of a designated object. The conclusion uses the actual canonical colimit legs, for all nonnegative degrees and all abelian sheaf diagrams; there is no scheme, terminal object, finite-limit, subcanonical, or monomorphism-transition assumption added. The new node is the lower-level sections criterion of 0738(2),(4), not a claim about higher cohomology. Its quasi-compactness clause is the finite-image-refinement definition from the source, rather than the stronger assertion that a literal finite subfamily covers. Its data, index category, colimit and canonical map are introduced in the statement, with site/cohomology and colimit definition references. It has no proof or proof dependencies.

For step 1 I opened the new node and def-weil-pbc-sites-and-cohomology. The former's isomorphism clause asks for a cofinal finite-cover system with quasi-compact pairwise overlaps. Each object of B is quasi-compact because its finite refining family maps to the original family with finite image; applying that same argument to each pairwise overlap verifies exactly those hypotheses. The latter definition explicitly says H^0(U,F)=F(U). Those two statements therefore give precisely the degree-zero canonical comparison. I did not apply the existing globally finite-cover theorem to a site with possibly infinite covers.

For step 2 I opened def-weil-pbc-site-cech-complex, lem-weil-pbc-filtered-colimits-commute-finite-limits, lem-weil-pbc-site-injective-cech-acyclic, and lem-weil-pbc-filtered-colimit-abelian-groups-exact. Their statements give, respectively, the finite product term and alternating restriction differential, commutation of the finite product with filtered colimit in abelian groups, positive exactness for each injective abelian sheaf on a general site, and preservation of an exact triple by the small filtered colimit. All overlaps are in B by the actual item hypothesis, including repeated indices. I wrote differential compatibility component by component. Applying exactness directly to the three consecutive terms avoids silently invoking an uncited general homology-colimit comparison. We choose the common ambient universe containing the site, covering indices, abelian groups and small D, as in the cited general-site injective lemma. Only the given covering pullbacks and their iterates are used, not arbitrary finite products in every slice.

For step 3 I opened lem-weil-pbc-site-cech-vanishing-criterion, whose statement is the arbitrary-site version of 03F9. Each of its three hypotheses is individually checked in the proof text: membership of overlaps, cofinality of the same chosen covers, and all-positive-degree Cech vanishing from step 2. Thus its conclusion gives derived acyclicity of the colimit of any injective-valued D-diagram. This conclusion does not assume the colimit remains injective.

For step 4 I opened lem-cbc-sieve-module-sheaves-grothendieck, def-weil-pbc-sites-and-cohomology, lem-weil-pbc-site-abelian-sheaves-filtered-colimits-exact, lem-weil-pbc-filtered-colimit-abelian-groups-exact, and lem-weil-pbc-right-derived-filtered-colimit-successor. The first is an arbitrary-small-topology Mathlib leaf for module-valued sheaves: specializing to integers gives abelian sheaves, since the integer action is uniquely determined by addition. The proof writes this identification, and the covering-family/sieve sheaf-condition conversion, explicitly. Evaluation is additive and left exact by the definition node. The exact-colimit nodes provide the source and target exactness hypotheses; abelian groups have small colimits. The successor node says that preservation in degree n plus acyclicity of all colimits of injective diagrams in degree n+1 gives preservation in degree n+1. Step 3 proves its acyclicity hypothesis for all such diagrams, and the induction assumption quantifies over all diagrams, so the application is valid also at n=0. Its construction already contains the natural connecting ladder; no appeal to just a definition of a delta-functor supplies a missing naturality theorem. Its statement concludes preservation, hence the map induced by the original coprojections, not an arbitrary abstract isomorphism.

I tested the new statement and all steps when B is empty (the item's conclusion is vacuous), when an object admits an empty cover (every abelian sheaf has zero sections there), when a chosen cover has one member or repeated indices, when D has one object, for the constant zero diagram, and for a filtered diagram with non-injective transition maps. An empty chosen cover makes every nonnegative Cech term the zero group, so step 2 is still valid; the finite-product comparison includes the empty product. The injectivity clause for a quasi-compact object requires neither quasi-separatedness nor monomorphic transitions, just as 0738(2) states. No dimension or degree bound is hidden. I checked all new and cited statements against delivery-errors B through E: no hollow data, unnamed notion, inline hidden non-elementary comparison, proof hidden in a new unsplit node, cycle by design, or clause-only replacement of the induction. All steps are shorter than 2000 characters. The one substantial new input has its own independent hypotheses and only concerns ordinary sections; the higher-degree argument stays in the item. Citations quote the actual statements, not their proofs. The generic off-unit uses of the 03AW and 03F9 nodes are declared in split_report.tool_uses for maintainer review; the general successor node is already Lean-closed and the other generic inputs are Mathlib leaves.

The substantive correction during self-review was to drop proposed duplicate Grothendieck/functorial-injective nodes and use the existing general module-sheaf leaf and derived-successor node. No statement was weakened. I retained the original search log and item searches. The initial server-only review_split probe passed; the required complete delivery dry run is the final validation.

## Not duplicates

lem-sfb-site-quasi-compact-section-colimit vs aux-site-filtered-colimit-sections-inverse: requires every covering on the entire site to be finite; the new criterion allows arbitrary covers and only cofinal finite covers at the chosen object.

lem-sfb-site-quasi-compact-section-colimit vs aux-weil-pbc-affine-sections-colimit: is a full affine etale-site result; the new statement treats an arbitrary site object.

lem-sfb-site-quasi-compact-section-colimit vs lem-sfb-profinite-action-filtered-colimit-creation: is a construction of equivariant condensed module colimits on the profinite site, not a general-site objectwise criterion.

lem-sfb-site-quasi-compact-section-colimit vs lem-weil-pbc-colimit-of-sites-sections: concerns a colimit of varying sites with globally finite covers, not a fixed arbitrary site with a local objectwise criterion.

lem-sfb-site-quasi-compact-section-colimit vs lem-weil-pbc-colimit-site-scalar-section-comparison: is for a presented diagram of varying sites and normalized inverse-image transitions; those data are absent from the new fixed-site criterion.

lem-sfb-site-quasi-compact-section-colimit vs lem-weil-pbc-constructible-finitely-presented: is a finite-presentation result for constructible sheaves on qcqs etale sites, rather than arbitrary-object site sections.

lem-sfb-site-quasi-compact-section-colimit vs lem-weil-pbc-constructible-large-colimit-factorization: concerns factorization of a morphism from a constructible etale sheaf, rather than an arbitrary-site section comparison.

lem-sfb-site-quasi-compact-section-colimit vs lem-weil-pbc-etale-qcqs-cofinal-finite-coverings: constructs finite etale refinements of scheme objects, rather than proving a filtered-colimit sections comparison on an arbitrary site.

lem-sfb-site-quasi-compact-section-colimit vs lem-weil-pbc-etale-qcqs-sections-filtered-colimit: is a scheme-etale sections, local-lift or eventual-zero statement; its scheme hypotheses are absent from the new arbitrary-site criterion.

lem-sfb-site-quasi-compact-section-colimit vs lem-weil-pbc-etale-section-colimit-eventual-zero: is a scheme-etale sections, local-lift or eventual-zero statement; its scheme hypotheses are absent from the new arbitrary-site criterion.

lem-sfb-site-quasi-compact-section-colimit vs lem-weil-pbc-etale-section-colimit-eventual-zero-finite-cover: is a scheme-etale sections, local-lift or eventual-zero statement; its scheme hypotheses are absent from the new arbitrary-site criterion.

lem-sfb-site-quasi-compact-section-colimit vs lem-weil-pbc-etale-section-colimit-finite-zero-cover: is a scheme-etale sections, local-lift or eventual-zero statement; its scheme hypotheses are absent from the new arbitrary-site criterion.

lem-sfb-site-quasi-compact-section-colimit vs lem-weil-pbc-etale-section-colimit-local-lifts: is a scheme-etale sections, local-lift or eventual-zero statement; its scheme hypotheses are absent from the new arbitrary-site criterion.

lem-sfb-site-quasi-compact-section-colimit vs lem-weil-pbc-etale-section-colimit-local-zero-sieve: is a scheme-etale sections, local-lift or eventual-zero statement; its scheme hypotheses are absent from the new arbitrary-site criterion.

lem-sfb-site-quasi-compact-section-colimit vs lem-weil-pbc-etale-section-colimit-representative: is a scheme-etale sections, local-lift or eventual-zero statement; its scheme hypotheses are absent from the new arbitrary-site criterion.

lem-sfb-site-quasi-compact-section-colimit vs lem-weil-pbc-exact-coefficient-affine-section-naturality: asserts naturality of affine coefficient-change comparisons along scheme maps, rather than a fixed-site filtered section criterion.

lem-sfb-site-quasi-compact-section-colimit vs lem-weil-pbc-exact-coefficient-affine-sheafification: is an affine etale evaluation/sheafification comparison for coefficient change; it assumes scheme affineness absent from the new node.

lem-sfb-site-quasi-compact-section-colimit vs lem-weil-pbc-filtered-module-sheaf-colimit-local-representatives: provides local representatives on a covering sieve only; the new theorem gives global section injectivity and, with extra finite-overlap hypotheses, bijectivity.

lem-sfb-site-quasi-compact-section-colimit vs lem-weil-pbc-finite-presieve-filtered-colimit: asserts closure of the sheaf condition for one finite presieve in presheaf colimits; it does not identify sheaf colimit sections under a local cofinal-cover criterion.

lem-sfb-site-quasi-compact-section-colimit vs lem-weil-pbc-fixed-site-degree-zero-representatives: requires globally finite covering presieves and asserts only representatives; the new node is local at one object and includes injectivity.

lem-sfb-site-quasi-compact-section-colimit vs lem-weil-pbc-grothendieck-affine-global-section-colimit: is continuity on an inverse system of affine schemes, rather than a local criterion for any site.

lem-sfb-site-quasi-compact-section-colimit vs lem-weil-pbc-grothendieck-etale-relative-section-colimit: is relative-section continuity along inverse limits of schemes, not the fixed-site objectwise criterion.

lem-sfb-site-quasi-compact-section-colimit vs lem-weil-pbc-grothendieck-etale-section-colimit: is continuity along an inverse system of qcqs schemes and its limit, not arbitrary fixed-site filtered coefficient colimits.

lem-sfb-site-quasi-compact-section-colimit vs lem-weil-pbc-grothendieck-hypercover-section-colimit: is a common-base continuity assertion for later-stage pullback complexes of a finite split hypercover, not fixed-site sections of a coefficient colimit.

lem-sfb-site-quasi-compact-section-colimit vs lem-weil-pbc-proetale-closed-abelian-filtered-colimits: is specific to a scheme pro-etale site and its closed/open immersions or finitely presented modules; it does not cover arbitrary site objects.

lem-sfb-site-quasi-compact-section-colimit vs lem-weil-pbc-proetale-qcqs-fp-section-calculus: is specific to a scheme pro-etale site and its closed/open immersions or finitely presented modules; it does not cover arbitrary site objects.

lem-sfb-site-quasi-compact-section-colimit vs lem-weil-pbc-proetale-ringed-filtered-colimits: is specific to a scheme pro-etale site and its closed/open immersions or finitely presented modules; it does not cover arbitrary site objects.

lem-sfb-site-quasi-compact-section-colimit vs lem-weil-pbc-proetale-ringed-open-closed: is specific to a scheme pro-etale site and its closed/open immersions or finitely presented modules; it does not cover arbitrary site objects.

lem-sfb-site-quasi-compact-section-colimit vs lem-weil-pbc-sets-section-lift-affine: is section lifting along a limit of schemes with affine transitions, not evaluation of a coefficient colimit on a fixed arbitrary site.

lem-sfb-site-quasi-compact-section-colimit vs lem-weil-pbc-sets-section-lift-local-family: is section lifting along a limit of schemes with affine transitions, not evaluation of a coefficient colimit on a fixed arbitrary site.

lem-sfb-site-quasi-compact-section-colimit vs lem-weil-pbc-sheaves-directed-colimit-sections: is restricted to open-subset sites of topological spaces and directed sets; the new node allows arbitrary sites and small filtered categories.

lem-sfb-site-quasi-compact-section-colimit vs lem-weil-pbc-site-filtered-colimit-sections-finite-coverings: requires every covering on the entire site to be finite; that hypothesis is not present in this item or new node.

lem-sfb-site-quasi-compact-section-colimit vs sbc-lem-higher-image-affine-class-descent: concerns higher direct-image continuity or class descent on a varying inverse system of schemes; it gives no arbitrary fixed-site object criterion.

lem-sfb-site-quasi-compact-section-colimit vs sbc-lem-higher-image-affine-class-vanishing: concerns higher direct-image continuity or class descent on a varying inverse system of schemes; it gives no arbitrary fixed-site object criterion.

lem-sfb-site-quasi-compact-section-colimit vs sbc-lem-higher-image-affine-continuity: concerns higher direct-image continuity or class descent on a varying inverse system of schemes; it gives no arbitrary fixed-site object criterion.

lem-sfb-site-quasi-compact-section-colimit vs sbc-lem-higher-image-local-class-vanishing: concerns higher direct-image continuity or class descent on a varying inverse system of schemes; it gives no arbitrary fixed-site object criterion.

lem-sfb-site-quasi-compact-section-colimit vs stage3-finite-hypercover-colimits: requires the topology globally to be generated by finite one-hypercovers; the new criterion is at one object and puts no global finitary-topology hypothesis on the site.

