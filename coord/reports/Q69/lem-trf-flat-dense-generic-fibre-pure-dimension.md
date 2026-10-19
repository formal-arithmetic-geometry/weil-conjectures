# Q69 stage-1 delivery: lem-trf-flat-dense-generic-fibre-pure-dimension

## Files written

- dag/nodes/sec-trace-formula/lem-trf-flat-dense-generic-fibre-pure-dimension.json: statement, split into six steps; unchanged statement; no exact Mathlib match.
- dag/nodes/sec-trace-formula/lem-trf-flat-fibre-component-closure-dimension.json: new statement-only unsplit geometric lemma; no exact Mathlib match. It gives the dimensions of the fibres of a single component closure inside a flat ambient family, without assuming that the closure itself is flat.
- citations.json: verbatim statements supporting every citation of every item proof step.

## Attachments

None. I searched WeilConjectures/ in the read-only slopmaster2 source for the exact blueprint tag, flat/dense/generic-fibre terminology, equidimensionality, and relative/fibre component dimension. The relevant source results concern smooth relative dimension, Noether normalization or finitely presented families with geometrically reduced fibres, not this statement. Upstream master is reference material only. The item has no lean_audit record of a matching finished declaration.

## Literature wanted

None. All source material needed for this split is present.

## Corrections and scope

The imported statement is true as written; no STATEMENT-DISPUTED and no statement change. Stacks 0GSK is explicitly a remark saying that the conclusions can be carefully proved if needed, not a complete argument to cite as a black box. I expanded that argument using 0GSJ and affine going down. In particular, one cannot assume that a reduced horizontal component closure of X is flat, and one cannot assert that an irreducible fibre component lies in one member of an infinite closed cover. Step 2 instead uses its generic point and maximality directly. The new lemma is the genuine component-closure input of 0GSJ; it applies even when the base is not integral, when the original fibre is not pure, and when the closure is not flat. Its proof is left to its later stage-1 item, as required for new nodes.

The density assumption is retained, although the given flatness already gives a generalization over the generic point for every point of X. There is no finite-presentation, Noetherian-base, properness, reduced-fibre or smoothness assumption in the ordinary-fibre argument. Local Noetherianity is used only on geometric fibres over fields in the final component criterion.

The unit is sk-i-curve-zero, and this dimension tool serves the existing semistable-alteration branch of the ancestor lem-trf-local-term-locality, via the flatification node. I did not change the chapter, unit, ancestry or route. Generic off-unit tools are declared in split_report.tool_uses; they support that branch and do not replace a unit step.

## Search audit

I searched the whole DAG for 0GSI, 0GSJ, 0GSK, 02NJ and 02NK, for equidimensionality and fibre-component specialization, and read the relevant candidate statements. I ran blueprint_refs.py ancestor for the item and searches for flat/dense generic-fibre dimension, generalizing, associated equidimensional, fibre dimension, closure fibre component, 0GSJ, equidimensional, 0GSI, and flat specialization. No blueprint node states the new lemma. The same_as fields remain empty. The ancestor and existing via chain are preserved; the new node prepends the item to that chain.

All additional Mathlib searches were made with msearch.py and are recorded in searches.jsonl. For the new node, two LeanFinder phrasings and LeanSearch searched fibre-component closures, Loogle searched Flat with LocallyOfFiniteType, and grep searched equidimensional/relativeDimension/pure dimension. All services ran. I read the hits: Flat.generalizingMap and HasGoingDown.of_flat give lifts, not component-closure dimension; UniversallyOpen.of_flat additionally assumes finite presentation and does not give dimension; SmoothOfRelativeDimension imposes smoothness; Jacobson-fibre and finite-morphism results do not give the conclusion. I read the local Mathlib Smooth.lean relative-dimension class and UniversallyOpen.lean generalizing result, and searched the project geometry/ring-theory sources. Existing ring going down is reused, rather than making a node for its elementary affine scheme application. The item's earlier Q12 searches are preserved, with the searches from this attempt appended. No unavailable search was recorded as a negative result.

## Not duplicates

lem-trf-flat-fibre-component-closure-dimension vs lem-trf-flat-dense-generic-fibre-pure-dimension: the new lemma concerns fibres of a single closure inside a flat ambient family; that closure need not be flat, the base need not be integral, and the starting fibre need not be pure. The item concerns all components of the ambient X_s under pure generic-fibre hypotheses. Its steps must lift a generic point, select its generic-fibre component, and prove the maximal-component identification before the lemma applies; the lemma does not assert either clause of the item.

lem-trf-flat-fibre-component-closure-dimension vs lem-trf-flatification-horizontal-curve-pair: the latter constructs a blowup and two simultaneous flat strict transforms with dimensions 1 and 0, and cites the item as its dimension tool. The new lemma constructs no blowup and gives the dimension of a fibre in one closure inside a flat family.

lem-trf-flat-fibre-component-closure-dimension vs lem-trf-dejong-relative-marked-semistable: the latter constructs a marked semistable alteration with nodal curve fibres; the new node assumes only an ambient flat locally finite type morphism and asserts a dimension equality for a component closure. The 0GSJ mention in that existing node's history/proof material is not its statement.

lem-trf-flat-fibre-component-closure-dimension vs lem-sbc-flat-fibre-component-dimension-specialization: the latter assumes local finite presentation and compares the local dimensions of the ambient fibres at two specializing points, with the special point generic in an ambient fibre component. The new node assumes only local finite type and computes dimensions inside the closure of a chosen component of an arbitrary fibre, whose special-fibre components may lie inside larger ambient components. Neither statement subsumes the new node.

lem-trf-flat-fibre-component-closure-dimension vs lem-sbc-cohen-macaulay-equidimensional-fibre-pieces: the existing node assumes a flat locally finitely presented morphism and partitions an open subset of its relative Cohen--Macaulay locus by component dimension. The new lemma assumes no Cohen--Macaulayness or finite presentation and studies one fibre-component closure, whose map need not be flat. The Tag 02NJ overlap only names relative dimension.

lem-trf-flat-fibre-component-closure-dimension vs lem-sbc-cohen-macaulay-fibre-dimension-decomposition: the existing node decomposes a relative Cohen--Macaulay locus into opens of constant fibre dimension, assuming finite presentation. It does not assert dimension equality along the closure of an arbitrary fibre component under merely local finite type.

lem-trf-flat-fibre-component-closure-dimension vs lem-sbc-flat-fibre-dimension-near-zero-dimensional-stalk: the existing node assumes local finite presentation and a zero-dimensional ambient fibre stalk and produces a neighbourhood of constant ambient fibre dimension. The new node concerns a selected component closure, assumes only local finite type, and does not produce a neighbourhood.

lem-trf-flat-fibre-component-closure-dimension vs lem-sbc-flat-fibre-dimension-strata-core: the existing node assumes local finite presentation and produces fibrewise dense opens on which ambient local fibre dimension is constant. It does not identify the dimensions of components of fibres of one chosen closure.

## Review by Q69

I read the item source in more-morphisms.tex: 0GSK (remark-flat-equidimensional), second list; 0GSJ (lemma-flat-associated-equidimensional); and the full 0GSI (lemma-associated-point-specializes) statement and proof. I also checked the official Stacks pages for 0GSK and 0GSJ. For the new node, 0GSJ applied to F=O_X is applicable: a fibre is locally of finite type over a field, hence locally Noetherian, so a component generic point is associated to its structure sheaf; O_X is quasi-coherent of finite type and flat over S by the flatness of f. The reduced closure Y and reduced image closure T are those of 0GSJ. Its relative-dimension conclusion gives the new node's equality; the reference fibre Y_t has precisely the underlying component B. No property of a reduction of a flat scheme is being used to claim flatness. This is a substantial separate input, and the new node has only a statement, no embedded proof.

I read each cited node's statement and generated citations.json from those exact statements. Step 1 takes existence of the generic point from lem-sc-scheme-sober, the fibre subspace identification from def-pc-scheme-fibre, integral affine coordinate domains from def-pc-integral-scheme, affine flatness from lem-weil-pbc-flat-morphism-affine-criterion, and exactly the prime-chain lift from lem-sc-flat-going-down. I checked the 00HS source in algebra.tex: (0) is prime because A is a domain, and it is below the contraction of the chosen prime of R. No lifting over a point outside the affine neighbourhood is used: every nonempty base open contains eta.

Step 2 uses lem-sc-irreducible-components-cover to choose B, sobriety to choose z, and the fibre-homeomorphism and component definitions to identify C inside Z_s. Each cited statement says exactly this. The only uncited argument is the written-out topology: a closed subset containing a generic point contains its closure, and maximality among irreducible subsets remains maximality in a closed subspace containing that subset. This is elementary. I explicitly avoided taking a component from an infinite covering of the whole fibre.

Step 3 uses only the new component-closure lemma: its f, t, y, s and D are respectively the original f, eta, z, the chosen s, and C. Step 2 verifies its component condition, and the item's hypothesis gives dim B=d. Thus this step does not take properties from the new lemma's intended proof or from the source without a node.

Step 4 uses lem-weil-pbc-lft-base-change to obtain a locally algebraic ordinary fibre and lem-sbc-equidimensional-open-local-dimension with the whole open; its hypotheses are exactly the purity already proved and d in the natural numbers. I read Varieties 0A21 parts (3) and (5) in varieties.tex. Step 5 uses the full statement of lem-sc-fibre-dimension-after-base-change, including its fibre identification and its pointwise local-dimension equality, for Spec Omega -> S. I read Morphisms 02FY(1) in morphisms.tex; it needs only local finite type and permits this arbitrary field extension.

Step 6 uses base-change local finite type again, pqf-def-locnoeth for the field's affine Noetherian cover, pqf-lem-locnoeth-lft for the geometric fibre, and lem-sbc-constant-local-dimension-components with O equal to the whole geometric fibre. I checked Morphisms 01T6 and the exact hypotheses of the last criterion. Field ideals prove the Noetherian-field premise directly. I read Morphisms 02NJ/02NK, whose component notion agrees with the unchanged item. The integer d is finite throughout, as required by the local-to-component criterion. No assertion confuses the dimension of a local ring with local topological dimension.

Small cases checked: empty X and empty special fibres (vacuous); a field base (the ordinary-fibre conclusion is the hypothesis); finite flat families (d=0); A^d over an integral base; a reducible flat curve family xy=t over a DVR (two special components but both have dimension 1); and a component closure in a reducible fibre. The new lemma permits empty Z_s. Its starting component B is nonempty by definition, and it imposes no equidimensionality on the other components. Flatness cannot be omitted even with a dense generic fibre: the blowup of the affine plane at the origin over the affine plane has generic fibre a point (d=0) but exceptional fibre P^1 of dimension 1. Its generic point is dense because the blowup is integral. I also checked all six non-elementary/elementary classifications: no step exceeds 2000 characters, no hidden comparison lemma is being proved inline, and every non-elementary input is a cited statement. B--E checks revealed no statement repair; the main repair relative to the imported empty proof is making the closure-component argument explicit and distinguishing it from ambient-flat equidimensionality.

## Unfinished work

No unfinished work in the item's one-level split. The single new lemma remains unsplit deliberately, for a later stage-1 worker. No Lean was written and no compiler, Lake or build tool was run.

## Validation

The server dry run passed preflight, check_dag and review_split on 2026-10-18. Its initial local duplicate-check diagnostic was repaired by reading and distinguishing the four additional 02NJ candidates above. A final report-only correction replaced an inapplicable nonflat vertical-component test with the blowup example, which also satisfies generic-fibre density; the final dry run is repeated after that correction.
