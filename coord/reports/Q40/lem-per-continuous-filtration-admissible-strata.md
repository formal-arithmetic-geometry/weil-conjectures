# Stage-1 report: lem-per-continuous-filtration-admissible-strata

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-continuous-filtration-admissible-strata.json: statement node, split in seven steps; no Mathlib match for the item.
- citations.json: seventeen step/node citations copied verbatim from the live cited statements.
- report.md: this report. searches.jsonl is the search command's own log; the two sandbox Python scripts only write this item's split and citation manifest.

New nodes: 0. New Mathlib leaves: 0. The existing generic filtration, comparison and geometry nodes suffice.

## Attachments

None. Searches of lean/WeilConjectures for the blueprint tag and for continuous/constructible filtrations found no declaration stating the item. I read AlgebraicGeometry.Etale.exists_filtration_isFiniteLocallyConstant in ConstructibleSheaf/Devissage.lean: it assumes a finite coefficient ring and concerns the small etale site. It is not this continuous E-coefficient assertion. The more general internal condensed filtration already has a DAG node, lem-sfb-finite-model-stratum-filtration, which the proof cites rather than claiming a new attachment.

## WANTED

None. All sources needed here are present.

## Audit of the item and blueprint

The live item had its full statement but no proof. Its statement is retained verbatim; no target, coefficient category, or hypothesis changes. The sandbox initially contained no node or earlier report. There is no released repair record for this item.

I read GOAL.md, the chapter and unit records, the current main-20261015 ancestor statement and proof, and the parent rational-stratum-integral-models node. This is the continuous coefficient devissage required below the ancestor's first paragraph (cohomology pullback and support). The parent explicitly names lem-sfb-finite-model-stratum-filtration. Applying that tool respects this route and creates no new copy of its theorem.

The original definition of internal/sectionwise module equivalence says that underlying abelian sheaves and restrictions are retained. It does not assert the functor and adjunction comparisons needed by the item. I therefore cite the existing theorem lem-sfb-internal-module-operations-transport for those comparisons, including counits and exactness. This avoids the definition-as-theorem error C4.

The item refers to continuous integral constructibility as background but asks for a rational filtration, not integral lattices or completed degree-zero models. Those later assertions belong to its parent and sibling integral-piece-completion-normalization. I introduce neither a lattice claim nor a completeness assumption here.

The Mathlib searches in this sandbox were made with msearch.py, with both semantic phrasings, Loogle, source grep, and LeanSearch; all six completed successfully. Their exact queries and returned names are appended to the item; the seven inherited records are retained. The semantic hits concern Noetherian spaces, finite generation/presentation, and sheaf constructions. Grep also locates the pro-etale site and ell-adic coefficient sheaf files, which I read: neither states the item. No search failure was called absence. Blueprint searches for filtration, common stratification, continuous coefficient, and filtration admissible, together with whole-DAG searches, supplied the reusable nodes.

## Not duplicates

No new node was created. In particular this delivery does not duplicate lem-sfb-finite-model-stratum-filtration, det-lem-coefficient-heart-filtration, or det-lem-coefficient-heart-common-stratification. The first is used directly and is stronger in its allowed coefficient rings; the item's additional continuous realization, lisse and geometric conclusions are assembled around it. Nor is an elementary closed-subscheme Noetherianity node created: its quotient-ideal argument stays in Step 5.

## Review by Q40

I read Bhatt–Scholze, Section 6.8, Lemma 6.8.2, Definitions 6.8.3, 6.8.6 and 6.8.10, Lemma 6.8.13, Proposition 6.8.14 and Remark 6.8.15. The definitions distinguish continuous rational lisse models from integral finite scalar models. The finite-stratum reduction in the proof of Lemma 6.8.13 motivates exactly this filtration. The additional detailed filtration theorem is an existing generic sheaf tool, not a claim that Bhatt–Scholze explicitly prove every strengthened geometric clause. I marked the assembly proof as agent-written. I also read Stacks topology.tex Tag 09Y5 (lemma-noetherian-partition-refined-by-stratification), Tag 0055 (definition-Krull and its following open-monotonicity remark), and properties.tex Tags 01OZ, 01OW and 02IK, including 02IK's omitted-details hint. No SGA source is used.

For Step 1 I opened all five cited statements. The Noetherian topology node gives the minimal-element assertion, which excludes a strict descending chain by applying it to the chain's terms. Continuous-coefficient-realizations gives a ring comparison isomorphism for the totally disconnected coefficient E, with the scalar-map compatibility; immersion-restriction identifies the inverse-limit and localized sheaves and locally closed restrictions. The internal-module equivalence retains the underlying abelian sheaves. Constructibility is used exactly as sk-def-sfb-constructible defines it: finite scalar models on finite locally closed strata. I wrote the finite-basis tensor maps and inverses explicitly; no tensor-product sections assertion is assumed.

For Step 2 I read the whole statement of lem-sfb-finite-model-stratum-filtration. It asserts reduced closed strata, monic counits, the precise quotient formula, finite constant local models, and qcqs opens and complements. It assumes only Noetherian underlying topology, which Step 1 gives. It does not require finite type over a field or an integral coefficient ring. Its fixed small-site universe agrees with that of this item. This theorem is existing material, so using it is not a relabelled new node.

For Step 3 I checked the field clause of lem-sfb-scalar-finite-free-resolutions: it applies to each finitely presented E-module P and gives a finite scalar basis, including P=0. Tensoring a specified isomorphism and its inverse and applying Step 1's coordinate maps gives the claimed free sheaf model. No local freeness is inferred merely from finite presentation over an arbitrary continuous-function ring; the matrix comes from the scalar field E.

For Step 4 I read lem-sfb-internal-module-operations-transport and verified that its conclusions include the actual inverse/direct/open functors, specified adjunction units and counits, and an additive exact equivalence. I also reread the continuous restriction theorem and the statement of proetale-ringed-open-closed: the former fixes the ring restriction maps; the latter says actual sectionwise open extension is left adjoint to inverse image. Every open-complement quasi-compactness hypothesis is already supplied by Step 2. Thus comparison identifies the very monomorphism defining the subobject and identifies its cokernel; an abstract equivalence of unrelated module categories would not suffice.

For Step 5 I checked the open-subscheme Noetherianity statement, the affine-quotient clause of def-weil-closed-immersion, the finite-ideal-generators definition of a Noetherian ring, and the affine-cover definition of locally Noetherian. The preimage of an ideal in R/I is finitely generated in R, and its generator images generate that ideal. The closed-subspace quasi-compactness argument adds the open complement to the cover. These are elementary arguments from the cited statements and definitions; 02IK's omitted proof is not silently invoked as an uncited non-elementary result.

For Step 6 I checked the open dimension bound, which is actually about open subspaces (not arbitrary maps). The closed immersion definition gives a homeomorphism onto a closed subset, so an irreducible closed chain of S is a chain of V; strictness is preserved. Thus dimension is bounded without assuming equidimensionality. Open immersion identifies local rings, and a ring map sends the displayed inverse of ell to an inverse. This proves invertibility on closed strata even when X is nonreduced.

Step 7 uses only the empty-cover sheaf axiom. I tested the assembly on the empty scheme (m=0), a point with F=0 or E^r, disconnected schemes with different local ranks, a DVR spectrum stratified into its generic and closed points, and a nonreduced scheme with the same two-stratum topology. The argument does not demand strictly increasing filtration subobjects or a nonzero local rank, and never factors an arbitrary scheme map through a stratum merely from containment of images. The actual reduced strata and their models come from the existing filtration statement.

All proof steps are shorter than 2000 characters. Every non-elementary input is in uses; proof_deps equals their union. I checked every citation against its node's statement and wrote the verbatim manifest. The generic off-unit tools are declared in split_report.tool_uses with reasons; I do not set the maintainer's tool_uses field. No node of another unit replaces a perverse/Fourier argument: these are solely coefficient, devissage and geometry tools below that argument. No item statement, import metadata, source history or blueprint ancestry is discarded.

## Unfinished work

None in this one-level split. Existing cited nodes remain responsible for their own downstream formalization. No new Lean was written and no compiler, Lake or build tool was run. Required dry-run and delivery results are recorded by deliver.py.
