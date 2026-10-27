# Worker report: lem-sfb-nonnegative-derived-totalization

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-nonnegative-derived-totalization.json: existing statement unchanged; four-step assembly, 2116 characters.
- dag/nodes/sec-six-functors-basics/lem-sfb-cosimplicial-injective-total-replacement.json: statement, unsplit; no exact or one-line Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-injective-finite-total-derived-comparison.json: statement, unsplit; no exact or one-line Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-resolved-total-comparison-descent.json: statement, unsplit; no exact or one-line Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-resolved-total-augmentation-square.json: statement, unsplit; no exact or one-line Mathlib match.
- citations.json: one verbatim quotation of the cited statement for each of the four assembly steps.

Attachments: none. The item tag and notion searches in lean/WeilConjectures found no project declaration stating the whole item; lean/Sheaf/CategoryTheory/NonnegativeDerivedTotalization.lean:234-237 states it with sorry. No source or Lean file was changed or compiled.

WANTED: none. All Stacks source files used here are present. The cosimplicial, naturality and augmented extensions are agent arguments; Tag 015J itself is not claimed to state them verbatim.

## Repair and preservation

The returned item had 7399 characters of proof in eight steps, too much work for one worker. This repair spreads that work into FOUR statement-only nodes, with independent self-contained hypotheses and no proof steps, proof dependencies, or sketches in their statements. The argument allocations have sizes 1966, 2264, 1978 and 1191 characters in the returned accounting. None of the new nodes states the entire parent theorem. The parent keeps its exact statement and its existing Lean record. The four tasks are the strict diagram replacement and signed total comparison; the injective finite-total calculation and inverse-unit normalization; the common-resolution descent and naturality argument; and the augmentation chain-map and derived square. The instructions requesting this explicit subdivision supersede the general caution about making nodes from clauses during ordinary splitting: these nodes expose the actual separate constructions, rather than four unnormalized restatements of the final result.

There were only launcher brief markers in the retained Q52 sandbox, no previous node/report/searches files. I copied the current live node, retained its old searches and all provenance and maintainer fields, saved its eight original proof steps verbatim as returned-proof.json, and saved the current prior N7 report verbatim as prior-report-N7.md. The complete old proof is ALSO retained below, with its task allocation, sources and dependencies. Thus all arguments survive the re-split and can be assigned to separate workers. No earlier search is claimed as freshly run; all new-node searches were actually run by msearch.py, whose searches.jsonl remains unedited. coord/dag-sync.md named by the inherited historical brief is absent in this live clone; the current direct-delivery brief controls the paths and scope.

I corrected three drafting details before delivery: every intermediate object of an admissible comparison zigzag is explicitly required to remain a columnwise quasi-isomorphic replacement of K; postcomposition is written I∘C rather than C∘I, and the three-index reassociation explicitly assumes that the cosimplicial operators preserve both internal indices and commute with both internal differentials. The latter is needed to speak of that strict tricomplex at all; it does not change the parent, which only asserts finiteness when such a resolution index is added.

## Repair of landing refusal (2026-10-22)

The return for reviewed head 9d5e66c62f3 reports a side/live promotion mismatch, not a mathematical rejection. I continued the retained approved split and its logged searches. Before changing anything I checked that no delivery process for this item remained active, read the durable dry-run receipts, and ran the required fresh dry run. It exited successfully at 6ca05086c1b against the current origin/sheaf-dag; this uses the delivery tool's current-base rebuild, rather than attempting to land the returned commit again.

I compared all five retained node files with the current read clone. The four new node ids remain absent there. The parent's current eight-step proof is exactly the saved returned-proof.json, and its statement, statement dependencies, source, blueprint, Lean record and maintainer metadata match the retained item. The only parent differences are our four-step proof, its four dependencies and its split report. The released stage-1 repair order is still present with keep_plan=true and still requires at least two new statement-only nodes and an assembly of at most 3000 characters, so the old reviewed split does not supersede this repair. The four retained nodes and all their search logs are preserved; I updated the parent's split report to identify this current-base repair explicitly.

I re-read the current statements of all six existing definition dependencies and all four statements cited by the assembly. Step 1 still obtains a nonnegative strict functorial replacement and the total quasi-isomorphism. Step 2 still obtains the normalized whole-derived-object comparison and the finite three-index reassociation. Step 3 still gives the naturality square and the augmentation-preserving common-resolution zigzag. Step 4 still supplies the actual degree-zero augmentation chain maps and their normalized derived square. All four citations.json quotes remain verbatim, and the assembly remains 2116 characters. No changed hypothesis requires a new mathematical argument or another search question.

I also re-read the five existing homological ingredient statements retained in the old argument: Grothendieck functorial injective embeddings, lower-bound-preserving functorial injective resolution, first-quadrant total column comparison, normalized derived injective-resolution naturality, and K-injective computation. The column comparison still has the fixed-second-index orientation, and the retained signed transposition is necessary. The resolution statement still supplies one functor for all lower bounds and diagrams; naturality still asserts the whole derived-object comparison with inverse-unit normalization. I re-opened Stacks 0141, 015J, 070J, 05TH, 079H and 0133 at the recorded labels. Thus no definition or tool statement invalidates any of the preserved arguments. The project theorem remains sorried, so there is no finished attachment. Zero diagrams, total degree zero, negative degrees, identity replacements and strict augmentations satisfy the stated hypotheses and formulas as checked above. Only stage-1 sandbox files were edited; no Lean was written or compiled.

## Sources and searches

I read AGENTS.md, roles/worker.md, GOAL.md, coord/brief-stage1.md, stages/1-dag.md, SETUP.md including its three blueprint levels, and delivery-errors.md B–E in full. I read the chapter and assigned unit records, and the current main-20261015 unit _section.md and direct-images.proof.md paragraph (3). This is a generic bounded-below homological construction below the open/direct-image route. The inherited ancestry command returns None; the inherited null ancestor is retained, with the exact current blueprint paragraph and the parent prepended to the via list for each new node. Neither the fixed chapter nor the unit's route is changed.

For the item and all four subarguments I read derived.tex Tag 015J, lemma-two-ss-complex-functor, especially proof remark (3) and the displayed equality Tot(F(I)) = F(Tot(I)). For the strict replacement and the common zigzag I read Tag 0141, lemma-functorial-injective-resolutions and remark-match, including J(0)=0 and the lower-bound-preserving double complex. I read injectives.tex Tag 079H, theorem-injective-embedding-grothendieck, and homology.tex Tag 0133, lemma-double-complex-gives-resolution, for its bounded diagonal hypotheses. For the finite-total comparison and descent I read derived.tex Tags 070J, lemma-bounded-below-injectives-K-injective, and 05TH, lemma-injective-acyclic. The augmentation task uses the same actual natural-resolution squares and the finite-total identity, with the degree-zero coface cancellation expanded in the retained argument. No SGA source is used.

Before creating nodes I searched the entire DAG by the tags 0141, 0133, 015J, 070J, 05TH and by cosimplicial/injective/replacement/total/zigzag terms; I read the closest statements, including the general functorial bounded resolution, K-injective comparison, normalized derived-resolution naturality, first-quadrant total comparison, CE total-resolution and injective-terms nodes, derived Cech-image totalization and the trace-formula compatible-roof lemma. Whole-blueprint searches were totalization, finite total, cosimplicial, injective resolution and augmentation. None states these same four tasks. The detailed same-tag comparisons follow below.

Each new node has LeanFinder (two distinct plain-language phrasings), Loogle, Mathlib grep, and LeanSearch queries, recorded exactly as executed. All those services answered. I read every returned hit. Object-level InjectiveResolution.of/isoRightDerivedObj and toRightDerivedZero naturality do not supply strict functorial resolutions of complex diagrams. injectiveResolutions lands only in the homotopy category. CM5b is a factorization for a fixed complex map, not the common diagramwise resolution theorem. isKInjective_of_injective gives one ingredient already represented by the existing K-injective node. total.mapIso maps a bicomplex isomorphism to a total isomorphism, and does not compare F(T(J)) with T(FJ). The additive finite-biproduct preservation and map_sum hits are ingredients in the summand calculation. Loogle's totalRightDerived hits mean the total derived FUNCTOR, rather than a complex total. Augmented simplex-category and Cech-conerve definitions do not give the derived augmentation square. The broad finite-total grep included irrelevant uses of function injectivity, so I additionally ran a focused grep in Algebra/Homology; it found no mapTotal or total/K-injective comparison. A file-restricted grep printed malformed path columns (the command's actual output is retained); I draw no declaration/line claim from it. No proposed new node is an exact Mathlib statement or a one-line specialization of these hits.

## Review by Q52

I checked the repair against every numbered point of the return: the parent statement is unchanged; the long argument is divided among four comparable tasks; all four are delivered unsplit, with their own statements, source places and executed searches; the parent proof is below 3000 characters; and every part of the old eight-step proof is retained below, not shortened away. This is a one-level stage-1 repair only.

For assembly step 1 I opened cosimplicial-injective-total-replacement: it explicitly supplies I, eta, strictness, the lift of every f, augmentation-object compatibility, and T(u) being a quasi-isomorphism. Its Grothendieck hypothesis is exactly the parent's hypothesis on A. The signed transposition uses (-1)^(nq); d_C and (-1)^q delta in the transposed total become (-1)^n d_C and delta after conjugation. The existing first-quadrant comparison can therefore be used in its actual fixed-second-index orientation when that new node is proved. No additivity of I is assumed: only functoriality is needed to retain cosimplicial identities.

For assembly step 2 I opened injective-finite-total-derived-comparison: its statement supplies the normalized whole-derived-object isomorphism, the inverse-unit formula, all column identifications, finite-biproduct comparison and finite-triple reassociation. The replacement from step 1 has exactly its required injective terms and columnwise quasi-isomorphisms. Finite sums of injectives are injective by componentwise extension across a monomorphism; since the total is nonnegative, 070J applies. The column isomorphisms are natural by the existing normalized-resolution-naturality statement, which I read: it explicitly gives a whole diagram of comparisons and inverse-unit normalization, not merely cohomology naturality. Thus the right side is an actual resolved total QT(FJ), with all coherent operators present.

For assembly step 3 I opened resolved-total-comparison-descent: it explicitly states both the strict-square naturality equation and the common zigzag, all mapped-total legs being quasi-isomorphisms, the equality e=chi_w chi_u^(-1), and its identity/composition laws. Step 1 supplies a square for every strict f, so there is no vacuous quantification over nonexistent lifts. The existing K-injective computation statement (1) compares columns under the original complex; the common zigzag lies entirely in nonnegative injective columns. Its I(u) and I(w) legs are quasi-isomorphisms by eta naturality and two-out-of-three, then F preserves their homotopy equivalences by additivity. The first-quadrant comparison is applied in B after F, with the same transposition sign. Normalized comparison naturality identifies each total leg with its map under RF(QT(K)); cancellation gives independence. I never assume F preserves arbitrary quasi-isomorphisms.

For assembly step 4 I opened resolved-total-augmentation-square: its statement introduces A,B,b,c,u,v and assumes u_n b_n=c_n v, exactly the square furnished by the simultaneous functorial resolution of step 1. It asserts the actual degree-zero total chain maps, their strict equation, the normalized derived square and compatible maps of augmented diagrams. I checked that d^0 c_0=d^1 c_0, so the coface part of the differential on a_J is zero; the internal differential commutes since c_0 is a chain map. Under beta, F(a_J) has F(c_0) only in cosimplicial degree zero. The specified inverse-unit column comparisons identify it with RF(Qb_n); this is the parent's totalized derived augmentation, not a newly chosen arrow. The descent lemma makes its square compatible with changes of resolutions.

The sources of the first task are 0141/079H/0133; of the second 015J/070J/05TH; of the third 0141/05TH/0133 and inverse-unit naturality; of the fourth 0141/015J with the explicit augmented chain square. All objects in the new statements are introduced, and their definition dependencies are listed. Each is strictly smaller than the parent: the first has no F, the second fixes an injective model and says nothing about choice descent or augmentation, the third assumes the normalized comparisons and treats their zigzags, and the fourth assumes a compatible resolved augmented square. Their proof/proof_deps are empty and status is unsplit. The old proof's complete arguments and cited ingredients are transferred below for their future workers.

Small cases: K=0 and the zero category give zero totals and the unique derived map; identity F gives the usual finite-sum comparison. A constant cosimplicial diagram has d^0=d^1 on its augmentation, hence zero alternating degree-zero coface differential. At total degree 0 there is one (0,0) summand, and for three indices one (0,0,0) summand, all with positive sign. In degree 1 the transposition changes the two differential contributions exactly as above; in negative degree all totals vanish. For identity replacements all descent arrows normalize to the identity. The zero augmentation satisfies the strict and derived squares. Unboundedness above causes no problem because each nonnegative diagonal is finite; no unbounded-below claim is made. No hypothesis on exact functors preserving injectives has been introduced.

Against B1–B10: statement-only tasks, self-contained objects, actual definition dependencies, TeX, source labels/tags, truthful logged searches, no false Mathlib leaves, checked blueprint provenance and no finished attachment. Against C1–C8: the four assembly steps use exactly the four opened statements (verbatim quotes in citations.json), no use of a cited proof in place of its statement, no omitted non-elementary input in the assembly, no cycle or route replacement, and no new off-unit proof citation. Against D1–D5: four separate work packages retain the full argument rather than moving everything to one node; their hypotheses make the assembly precise. Against E1–E7: checked lower bounds, injectivity, sign orientation, augmentation chain maps and the meaning of coherent resolved totals. There is no statement dispute or source correction. The assembly's longest step is under 700 characters; no non-elementary parent step is over 2000 characters.

## Not duplicates

lem-sfb-cosimplicial-injective-total-replacement vs lem-sc-finite-strip-cone-graded-map-epi: the existing statement concerns the filtration or graded cone map for a finite horizontal strip; it does not give a functorial strict cosimplicial injective replacement and signed total quasi-isomorphism.

lem-sfb-cosimplicial-injective-total-replacement vs lem-sc-finite-strip-cone-graded-map-isIso: the existing statement concerns the filtration or graded cone map for a finite horizontal strip; it does not give a functorial strict cosimplicial injective replacement and signed total quasi-isomorphism.

lem-sfb-cosimplicial-injective-total-replacement vs lem-sc-first-quadrant-total-column-comparison: the existing statement assumes a given double-complex map with quasi-isomorphic fixed-second-index columns and concludes only its total quasi-isomorphism; the new task concerns a functorial strict cosimplicial injective replacement and signed total quasi-isomorphism.

lem-sfb-cosimplicial-injective-total-replacement vs lem-sc-finite-strip-cone-filtration-graded-point: the existing statement concerns the filtration or graded cone map for a finite horizontal strip; it does not give a functorial strict cosimplicial injective replacement and signed total quasi-isomorphism.

lem-sfb-cosimplicial-injective-total-replacement vs lem-sc-finite-strip-row-augmentation: the existing statement proves a quasi-isomorphism from rowwise resolution hypotheses for a prescribed bicomplex augmentation; it does not give a functorial strict cosimplicial injective replacement and signed total quasi-isomorphism.

lem-sfb-cosimplicial-injective-total-replacement vs lem-sc-finite-strip-cone-filtration-steps: the existing statement concerns the filtration or graded cone map for a finite horizontal strip; it does not give a functorial strict cosimplicial injective replacement and signed total quasi-isomorphism.

lem-sfb-cosimplicial-injective-total-replacement vs lem-sc-first-quadrant-column-augmentation: the existing statement proves a quasi-isomorphism from rowwise resolution hypotheses for a prescribed bicomplex augmentation; it does not give a functorial strict cosimplicial injective replacement and signed total quasi-isomorphism.

lem-sfb-cosimplicial-injective-total-replacement vs lem-pc-abelian-cech-alpha-quasi-iso: the existing statement is the cover-specific global-section Cech augmentation quasi-isomorphism, whereas this task gives a functorial strict cosimplicial injective replacement and signed total quasi-isomorphism.

lem-sfb-cosimplicial-injective-total-replacement vs lem-sc-finite-strip-cone-graded-map-differential: the existing statement concerns the filtration or graded cone map for a finite horizontal strip; it does not give a functorial strict cosimplicial injective replacement and signed total quasi-isomorphism.

lem-sfb-cosimplicial-injective-total-replacement vs lem-sc-finite-strip-cone-filtration: the existing statement concerns the filtration or graded cone map for a finite horizontal strip; it does not give a functorial strict cosimplicial injective replacement and signed total quasi-isomorphism.

lem-sfb-cosimplicial-injective-total-replacement vs lem-sc-finite-strip-cone-graded-map-mono: the existing statement concerns the filtration or graded cone map for a finite horizontal strip; it does not give a functorial strict cosimplicial injective replacement and signed total quasi-isomorphism.

lem-sfb-cosimplicial-injective-total-replacement vs lem-sc-finite-strip-cone-filtration-graded: the existing statement concerns the filtration or graded cone map for a finite horizontal strip; it does not give a functorial strict cosimplicial injective replacement and signed total quasi-isomorphism.

lem-sfb-resolved-total-augmentation-square vs lem-sfb-nonnegative-derived-totalization: the parent requires all four constructions together, including existence, descent, naturality and augmentation; the new node isolates the derived degree-zero total augmentation equation for an arbitrary compatible resolved augmented square, as the explicit re-split return requires.

lem-sfb-resolved-total-augmentation-square vs lem-trf-derived-cech-diagram-functorial-modules: the existing statement gives the restriction roof for module sheaves and global sections across a scheme morphism, with only a columnwise assertion for the middle leg; this task gives the derived degree-zero total augmentation equation for an arbitrary compatible resolved augmented square.

lem-sfb-resolved-total-augmentation-square vs lem-weil-pbc-functorial-object-resolution: the existing statement constructs functorial object or bounded-complex injective resolutions; it has no mapped finite-total inverse-unit augmentation square, which is the new task.

lem-sfb-resolved-total-augmentation-square vs lem-weil-pbc-functorial-bounded-injective-resolution-totalization: the existing statement constructs functorial object or bounded-complex injective resolutions; it has no mapped finite-total inverse-unit augmentation square, which is the new task.

lem-sfb-resolved-total-augmentation-square vs lem-weil-pbc-functorial-bounded-injective-resolution: the existing statement constructs functorial object or bounded-complex injective resolutions; it has no mapped finite-total inverse-unit augmentation square, which is the new task.

lem-sfb-resolved-total-augmentation-square vs lem-pc-derived-direct-image-truncated-coproduct: the existing conclusion is about coproduct maps, their filtrations, exact couples or truncations of derived direct images; this task concerns the derived degree-zero total augmentation equation for an arbitrary compatible resolved augmented square without an indexed coproduct or truncation hypothesis.

lem-sfb-resolved-total-augmentation-square vs lem-pc-truncated-direct-image-second-page-coproduct-epi: the existing conclusion is about coproduct maps, their filtrations, exact couples or truncations of derived direct images; this task concerns the derived degree-zero total augmentation equation for an arbitrary compatible resolved augmented square without an indexed coproduct or truncation hypothesis.

lem-sfb-resolved-total-augmentation-square vs lem-pc-hypercohomology-edge-cocycle-canonical: the existing conclusion identifies a cohomology edge/cycle-quotient map; this task concerns the derived degree-zero total augmentation equation for an arbitrary compatible resolved augmented square in the entire derived category, with its actual chain model.

lem-sfb-resolved-total-augmentation-square vs lem-pc-truncated-direct-image-sheaf-coproduct-epi: the existing conclusion is about coproduct maps, their filtrations, exact couples or truncations of derived direct images; this task concerns the derived degree-zero total augmentation equation for an arbitrary compatible resolved augmented square without an indexed coproduct or truncation hypothesis.

lem-sfb-resolved-total-augmentation-square vs lem-pc-coproduct-truncation-couple: the existing conclusion is about coproduct maps, their filtrations, exact couples or truncations of derived direct images; this task concerns the derived degree-zero total augmentation equation for an arbitrary compatible resolved augmented square without an indexed coproduct or truncation hypothesis.

lem-sfb-resolved-total-augmentation-square vs def-pc-right-derived-single-degree-comparison: the existing statement is a shifted single-object right-derived-unit/homology comparison; it does not provide the derived degree-zero total augmentation equation for an arbitrary compatible resolved augmented square.

lem-sfb-resolved-total-augmentation-square vs lem-pc-hypercohomology-edge-cocycle: the existing conclusion identifies a cohomology edge/cycle-quotient map; this task concerns the derived degree-zero total augmentation equation for an arbitrary compatible resolved augmented square in the entire derived category, with its actual chain model.

lem-sfb-injective-finite-total-derived-comparison vs lem-sfb-nonnegative-derived-totalization: the parent requires all four constructions together, including existence, descent, naturality and augmentation; the new node isolates the whole-derived-object normalized finite-total comparison on a fixed injective diagram, as the explicit re-split return requires.

lem-sfb-injective-finite-total-derived-comparison vs lem-pc-derived-direct-image-truncated-coproduct: the existing conclusion is about coproduct maps, their filtrations, exact couples or truncations of derived direct images; this task concerns the whole-derived-object normalized finite-total comparison on a fixed injective diagram without an indexed coproduct or truncation hypothesis.

lem-sfb-injective-finite-total-derived-comparison vs lem-pc-truncated-direct-image-second-page-coproduct-epi: the existing conclusion is about coproduct maps, their filtrations, exact couples or truncations of derived direct images; this task concerns the whole-derived-object normalized finite-total comparison on a fixed injective diagram without an indexed coproduct or truncation hypothesis.

lem-sfb-injective-finite-total-derived-comparison vs lem-pc-hypercohomology-edge-cocycle-canonical: the existing conclusion identifies a cohomology edge/cycle-quotient map; this task concerns the whole-derived-object normalized finite-total comparison on a fixed injective diagram in the entire derived category, with its actual chain model.

lem-sfb-injective-finite-total-derived-comparison vs lem-pc-truncated-direct-image-sheaf-coproduct-epi: the existing conclusion is about coproduct maps, their filtrations, exact couples or truncations of derived direct images; this task concerns the whole-derived-object normalized finite-total comparison on a fixed injective diagram without an indexed coproduct or truncation hypothesis.

lem-sfb-injective-finite-total-derived-comparison vs lem-pc-coproduct-truncation-couple: the existing conclusion is about coproduct maps, their filtrations, exact couples or truncations of derived direct images; this task concerns the whole-derived-object normalized finite-total comparison on a fixed injective diagram without an indexed coproduct or truncation hypothesis.

lem-sfb-injective-finite-total-derived-comparison vs def-pc-right-derived-single-degree-comparison: the existing statement is a shifted single-object right-derived-unit/homology comparison; it does not provide the whole-derived-object normalized finite-total comparison on a fixed injective diagram.

lem-sfb-injective-finite-total-derived-comparison vs lem-pc-hypercohomology-edge-cocycle: the existing conclusion identifies a cohomology edge/cycle-quotient map; this task concerns the whole-derived-object normalized finite-total comparison on a fixed injective diagram in the entire derived category, with its actual chain model.

lem-sfb-injective-finite-total-derived-comparison vs lem-pc-grothendieck-hypercohomology-edge: the existing conclusion identifies a cohomology edge/cycle-quotient map; this task concerns the whole-derived-object normalized finite-total comparison on a fixed injective diagram in the entire derived category, with its actual chain model.

lem-sfb-injective-finite-total-derived-comparison vs lem-pc-natural-bounded-below-truncation-couples: the existing conclusion is about coproduct maps, their filtrations, exact couples or truncations of derived direct images; this task concerns the whole-derived-object normalized finite-total comparison on a fixed injective diagram without an indexed coproduct or truncation hypothesis.

lem-sfb-injective-finite-total-derived-comparison vs lem-pc-right-derived-canonical-single-unit-shift: the existing statement is a shifted single-object right-derived-unit/homology comparison; it does not provide the whole-derived-object normalized finite-total comparison on a fixed injective diagram.

lem-sfb-injective-finite-total-derived-comparison vs lem-pc-bounded-below-coproduct-filtration: the existing conclusion is about coproduct maps, their filtrations, exact couples or truncations of derived direct images; this task concerns the whole-derived-object normalized finite-total comparison on a fixed injective diagram without an indexed coproduct or truncation hypothesis.

lem-sfb-resolved-total-comparison-descent vs lem-sc-finite-strip-cone-graded-map-epi: the existing statement concerns the filtration or graded cone map for a finite horizontal strip; it does not give common strict cosimplicial-resolution zigzags and the normalized natural mapped-total identification.

lem-sfb-resolved-total-comparison-descent vs lem-sc-finite-strip-cone-graded-map-isIso: the existing statement concerns the filtration or graded cone map for a finite horizontal strip; it does not give common strict cosimplicial-resolution zigzags and the normalized natural mapped-total identification.

lem-sfb-resolved-total-comparison-descent vs lem-sc-first-quadrant-total-column-comparison: the existing statement assumes a given double-complex map with quasi-isomorphic fixed-second-index columns and concludes only its total quasi-isomorphism; the new task concerns common strict cosimplicial-resolution zigzags and the normalized natural mapped-total identification.

lem-sfb-resolved-total-comparison-descent vs lem-sc-finite-strip-cone-filtration-graded-point: the existing statement concerns the filtration or graded cone map for a finite horizontal strip; it does not give common strict cosimplicial-resolution zigzags and the normalized natural mapped-total identification.

lem-sfb-resolved-total-comparison-descent vs lem-sc-finite-strip-row-augmentation: the existing statement proves a quasi-isomorphism from rowwise resolution hypotheses for a prescribed bicomplex augmentation; it does not give common strict cosimplicial-resolution zigzags and the normalized natural mapped-total identification.

lem-sfb-resolved-total-comparison-descent vs lem-sc-finite-strip-cone-filtration-steps: the existing statement concerns the filtration or graded cone map for a finite horizontal strip; it does not give common strict cosimplicial-resolution zigzags and the normalized natural mapped-total identification.

lem-sfb-resolved-total-comparison-descent vs lem-sc-first-quadrant-column-augmentation: the existing statement proves a quasi-isomorphism from rowwise resolution hypotheses for a prescribed bicomplex augmentation; it does not give common strict cosimplicial-resolution zigzags and the normalized natural mapped-total identification.

lem-sfb-resolved-total-comparison-descent vs lem-pc-abelian-cech-alpha-quasi-iso: the existing statement is the cover-specific global-section Cech augmentation quasi-isomorphism, whereas this task gives common strict cosimplicial-resolution zigzags and the normalized natural mapped-total identification.

lem-sfb-resolved-total-comparison-descent vs lem-sc-finite-strip-cone-graded-map-differential: the existing statement concerns the filtration or graded cone map for a finite horizontal strip; it does not give common strict cosimplicial-resolution zigzags and the normalized natural mapped-total identification.

lem-sfb-resolved-total-comparison-descent vs lem-sc-finite-strip-cone-filtration: the existing statement concerns the filtration or graded cone map for a finite horizontal strip; it does not give common strict cosimplicial-resolution zigzags and the normalized natural mapped-total identification.

lem-sfb-resolved-total-comparison-descent vs lem-sc-finite-strip-cone-graded-map-mono: the existing statement concerns the filtration or graded cone map for a finite horizontal strip; it does not give common strict cosimplicial-resolution zigzags and the normalized natural mapped-total identification.

lem-sfb-resolved-total-comparison-descent vs lem-sc-finite-strip-cone-filtration-graded: the existing statement concerns the filtration or graded cone map for a finite horizontal strip; it does not give common strict cosimplicial-resolution zigzags and the normalized natural mapped-total identification.

lem-sfb-cosimplicial-injective-total-replacement vs lem-sp-derived-injective-resolution-naturality: the existing general statement gives normalized comparisons for specified bounded-below injective resolution squares, not a functorial strict cosimplicial injective replacement and signed total quasi-isomorphism; it is an ingredient for the subargument, not the same task.

lem-sfb-injective-finite-total-derived-comparison vs lem-sp-derived-injective-resolution-naturality: the existing general statement gives normalized comparisons for specified bounded-below injective resolution squares, not the whole-derived-object normalized finite-total comparison on a fixed injective diagram; it is an ingredient for the subargument, not the same task.

lem-sfb-resolved-total-comparison-descent vs lem-sp-derived-injective-resolution-naturality: the existing general statement gives normalized comparisons for specified bounded-below injective resolution squares, not common strict cosimplicial-resolution zigzags and the normalized natural mapped-total identification; it is an ingredient for the subargument, not the same task.

lem-sfb-resolved-total-augmentation-square vs lem-sp-derived-injective-resolution-naturality: the existing general statement gives normalized comparisons for specified bounded-below injective resolution squares, not the derived degree-zero total augmentation equation for an arbitrary compatible resolved augmented square; it is an ingredient for the subargument, not the same task.

Additional close matches: lem-sp-cartan-eilenberg-total-resolution constructs a total resolution of an ordinary bounded-below complex from termwise row resolutions. It does not retain a cosimplicial diagram of complexes or define beta and its derived normalization. lem-sp-ce-total-injective-terms supplies only injectivity of total terms, already one ingredient of the second task. lem-sfb-derived-cech-image-totalization is a geometric covering-descent assertion with exact inverse image; it does not state the generic homological constructions here. The functorial-bounded-resolution and K-injective computation nodes are reused as ingredients in the retained arguments, not reconstructed under new names.


The full dry run identified further same-tag nodes (the object-store baseline enumerates a different first twelve than the filesystem search). I opened each statement and added these comparisons:

lem-sfb-cosimplicial-injective-total-replacement vs lem-sp-cartan-eilenberg-cone-graded-hom-ext: The existing statement concerns retained-column generators detect maps from the graded piece for the cone of one prescribed bicomplex augmentation; it has no strict cosimplicial replacement or mapped derived-total comparison. The new statement concerns the strict cosimplicial replacement functor, its signed transposition and total quasi-isomorphism.

lem-sfb-cosimplicial-injective-total-replacement vs lem-sp-cartan-eilenberg-cone-graded-resolution-representative: The existing statement concerns graded differential on retained resolution representatives for the cone of one prescribed bicomplex augmentation; it has no strict cosimplicial replacement or mapped derived-total comparison. The new statement concerns the strict cosimplicial replacement functor, its signed transposition and total quasi-isomorphism.

lem-sfb-cosimplicial-injective-total-replacement vs lem-sp-cartan-eilenberg-cone-filtration-data: The existing statement concerns construction of pinned cone filtration steps for the cone of one prescribed bicomplex augmentation; it has no strict cosimplicial replacement or mapped derived-total comparison. The new statement concerns the strict cosimplicial replacement functor, its signed transposition and total quasi-isomorphism.

lem-sfb-cosimplicial-injective-total-replacement vs lem-sp-cartan-eilenberg-cone-filtration-data-steps: The existing statement concerns explicit cone steps are antitone and differential-stable for the cone of one prescribed bicomplex augmentation; it has no strict cosimplicial replacement or mapped derived-total comparison. The new statement concerns the strict cosimplicial replacement functor, its signed transposition and total quasi-isomorphism.

lem-sfb-cosimplicial-injective-total-replacement vs lem-sp-cartan-eilenberg-cone-graded-augmentation-representative: The existing statement concerns graded differential on retained augmentation representatives for the cone of one prescribed bicomplex augmentation; it has no strict cosimplicial replacement or mapped derived-total comparison. The new statement concerns the strict cosimplicial replacement functor, its signed transposition and total quasi-isomorphism.

lem-sfb-cosimplicial-injective-total-replacement vs lem-sp-cartan-eilenberg-cone-graded-normalized-iso: The existing statement concerns normalized degreewise quotient comparison for the augmented cone for the cone of one prescribed bicomplex augmentation; it has no strict cosimplicial replacement or mapped derived-total comparison. The new statement concerns the strict cosimplicial replacement functor, its signed transposition and total quasi-isomorphism.

lem-sfb-cosimplicial-injective-total-replacement vs lem-sp-cartan-eilenberg-cone-graded-short-complex-iso: The existing statement concerns short-complex comparison for the graded augmented cone for the cone of one prescribed bicomplex augmentation; it has no strict cosimplicial replacement or mapped derived-total comparison. The new statement concerns the strict cosimplicial replacement functor, its signed transposition and total quasi-isomorphism.

lem-sfb-cosimplicial-injective-total-replacement vs lem-sp-cartan-eilenberg-cone-graded-normalized-differential: The existing statement concerns adjacent differential compatibility of normalized column-cone maps for the cone of one prescribed bicomplex augmentation; it has no strict cosimplicial replacement or mapped derived-total comparison. The new statement concerns the strict cosimplicial replacement functor, its signed transposition and total quasi-isomorphism.

lem-sfb-cosimplicial-injective-total-replacement vs lem-sp-cartan-eilenberg-cone-filtration: The existing statement concerns pinned complex-degree filtration and column-cone graded cohomology for the cone of one prescribed bicomplex augmentation; it has no strict cosimplicial replacement or mapped derived-total comparison. The new statement concerns the strict cosimplicial replacement functor, its signed transposition and total quasi-isomorphism.

lem-sfb-cosimplicial-injective-total-replacement vs lem-sp-cartan-eilenberg-cone-filtration-properties: The existing statement concerns bounds and graded pieces of pinned cone filtration for the cone of one prescribed bicomplex augmentation; it has no strict cosimplicial replacement or mapped derived-total comparison. The new statement concerns the strict cosimplicial replacement functor, its signed transposition and total quasi-isomorphism.

lem-sfb-cosimplicial-injective-total-replacement vs lem-sp-cartan-eilenberg-cone-graded-split-injection: The existing statement concerns normalized retained-column split injection for the cone of one prescribed bicomplex augmentation; it has no strict cosimplicial replacement or mapped derived-total comparison. The new statement concerns the strict cosimplicial replacement functor, its signed transposition and total quasi-isomorphism.

lem-sfb-cosimplicial-injective-total-replacement vs lem-sp-cartan-eilenberg-augmentation-quasi-iso: The existing statement proves that a supplied ordinary complex-to-total augmentation is a quasi-isomorphism from rowwise hypotheses; it neither constructs a strict diagram replacement nor treats its derived-unit comparison. The new statement concerns the strict cosimplicial replacement functor, its signed transposition and total quasi-isomorphism.

lem-sfb-resolved-total-comparison-descent vs lem-sp-cartan-eilenberg-cone-graded-hom-ext: The existing statement concerns retained-column generators detect maps from the graded piece for the cone of one prescribed bicomplex augmentation; it has no strict cosimplicial replacement or mapped derived-total comparison. The new statement concerns the normalized strict-square equation and common cosimplicial-resolution zigzag.

lem-sfb-resolved-total-comparison-descent vs lem-sp-cartan-eilenberg-cone-graded-resolution-representative: The existing statement concerns graded differential on retained resolution representatives for the cone of one prescribed bicomplex augmentation; it has no strict cosimplicial replacement or mapped derived-total comparison. The new statement concerns the normalized strict-square equation and common cosimplicial-resolution zigzag.

lem-sfb-resolved-total-comparison-descent vs lem-sp-cartan-eilenberg-cone-filtration-data: The existing statement concerns construction of pinned cone filtration steps for the cone of one prescribed bicomplex augmentation; it has no strict cosimplicial replacement or mapped derived-total comparison. The new statement concerns the normalized strict-square equation and common cosimplicial-resolution zigzag.

lem-sfb-resolved-total-comparison-descent vs lem-sp-cartan-eilenberg-cone-filtration-data-steps: The existing statement concerns explicit cone steps are antitone and differential-stable for the cone of one prescribed bicomplex augmentation; it has no strict cosimplicial replacement or mapped derived-total comparison. The new statement concerns the normalized strict-square equation and common cosimplicial-resolution zigzag.

lem-sfb-resolved-total-comparison-descent vs lem-sp-cartan-eilenberg-cone-graded-augmentation-representative: The existing statement concerns graded differential on retained augmentation representatives for the cone of one prescribed bicomplex augmentation; it has no strict cosimplicial replacement or mapped derived-total comparison. The new statement concerns the normalized strict-square equation and common cosimplicial-resolution zigzag.

lem-sfb-resolved-total-comparison-descent vs lem-sp-cartan-eilenberg-cone-graded-normalized-iso: The existing statement concerns normalized degreewise quotient comparison for the augmented cone for the cone of one prescribed bicomplex augmentation; it has no strict cosimplicial replacement or mapped derived-total comparison. The new statement concerns the normalized strict-square equation and common cosimplicial-resolution zigzag.

lem-sfb-resolved-total-comparison-descent vs lem-sp-cartan-eilenberg-cone-graded-short-complex-iso: The existing statement concerns short-complex comparison for the graded augmented cone for the cone of one prescribed bicomplex augmentation; it has no strict cosimplicial replacement or mapped derived-total comparison. The new statement concerns the normalized strict-square equation and common cosimplicial-resolution zigzag.

lem-sfb-resolved-total-comparison-descent vs lem-sp-cartan-eilenberg-cone-graded-normalized-differential: The existing statement concerns adjacent differential compatibility of normalized column-cone maps for the cone of one prescribed bicomplex augmentation; it has no strict cosimplicial replacement or mapped derived-total comparison. The new statement concerns the normalized strict-square equation and common cosimplicial-resolution zigzag.

lem-sfb-resolved-total-comparison-descent vs lem-sp-cartan-eilenberg-cone-filtration: The existing statement concerns pinned complex-degree filtration and column-cone graded cohomology for the cone of one prescribed bicomplex augmentation; it has no strict cosimplicial replacement or mapped derived-total comparison. The new statement concerns the normalized strict-square equation and common cosimplicial-resolution zigzag.

lem-sfb-resolved-total-comparison-descent vs lem-sp-cartan-eilenberg-cone-filtration-properties: The existing statement concerns bounds and graded pieces of pinned cone filtration for the cone of one prescribed bicomplex augmentation; it has no strict cosimplicial replacement or mapped derived-total comparison. The new statement concerns the normalized strict-square equation and common cosimplicial-resolution zigzag.

lem-sfb-resolved-total-comparison-descent vs lem-sp-cartan-eilenberg-cone-graded-split-injection: The existing statement concerns normalized retained-column split injection for the cone of one prescribed bicomplex augmentation; it has no strict cosimplicial replacement or mapped derived-total comparison. The new statement concerns the normalized strict-square equation and common cosimplicial-resolution zigzag.

lem-sfb-resolved-total-comparison-descent vs lem-sp-cartan-eilenberg-augmentation-quasi-iso: The existing statement proves that a supplied ordinary complex-to-total augmentation is a quasi-isomorphism from rowwise hypotheses; it neither constructs a strict diagram replacement nor treats its derived-unit comparison. The new statement concerns the normalized strict-square equation and common cosimplicial-resolution zigzag.

lem-sfb-injective-finite-total-derived-comparison vs lem-sp-cartan-eilenberg-augmentation-quasi-iso: The existing statement proves that a supplied ordinary complex-to-total augmentation is a quasi-isomorphism from rowwise hypotheses; it neither constructs a strict diagram replacement nor treats its derived-unit comparison. The new statement concerns the K-injective finite-total computation with inverse-unit normalization and three-index reassociation.

lem-sfb-injective-finite-total-derived-comparison vs lem-sp-cartan-eilenberg-total-resolution: The existing statement gives a K-injective total resolution of one complex; it does not assert the K-injective finite-total computation with inverse-unit normalization and three-index reassociation.

lem-sfb-injective-finite-total-derived-comparison vs lem-sp-ce-acyclic-abutment: The existing statement concerns acyclic cartan--eilenberg total cohomology and image filtration for presentations attached to two composable functors F,G (with acyclicity hypotheses where stated), not the K-injective finite-total computation with inverse-unit normalization and three-index reassociation for a general strict cosimplicial diagram.

lem-sfb-injective-finite-total-derived-comparison vs lem-sp-ce-acyclic-augmentation: The existing statement concerns natural acyclic cartan--eilenberg augmentation for presentations attached to two composable functors F,G (with acyclicity hypotheses where stated), not the K-injective finite-total computation with inverse-unit normalization and three-index reassociation for a general strict cosimplicial diagram.

lem-sfb-injective-finite-total-derived-comparison vs lem-sp-ce-page-realization: The existing statement concerns functorial cartan--eilenberg page realization without acyclicity for presentations attached to two composable functors F,G (with acyclicity hypotheses where stated), not the K-injective finite-total computation with inverse-unit normalization and three-index reassociation for a general strict cosimplicial diagram.

lem-sfb-injective-finite-total-derived-comparison vs lem-sp-ce-total-injective-terms: The existing statement gives only injectivity and the lower bound of total terms. This is one input to the new task, which additionally states the K-injective finite-total computation with inverse-unit normalization and three-index reassociation.

lem-sfb-injective-finite-total-derived-comparison vs def-weil-pbc-ce-canonical-row-comparison: The existing definition constructs canonical normalized ce row comparison for a specified etale termwise hypercohomology presentation and truncation (or row comparison); it does not prove the K-injective finite-total computation with inverse-unit normalization and three-index reassociation.

lem-sfb-injective-finite-total-derived-comparison vs def-weil-pbc-etale-filtered-step-cohomology-iso: The existing definition constructs canonical filtered-step derived-cohomology comparison for a specified etale termwise hypercohomology presentation and truncation (or row comparison); it does not prove the K-injective finite-total computation with inverse-unit normalization and three-index reassociation.

lem-sfb-injective-finite-total-derived-comparison vs def-weil-pbc-etale-restricted-augmentation: The existing definition constructs explicit restricted augmented-total map for a specified etale termwise hypercohomology presentation and truncation (or row comparison); it does not prove the K-injective finite-total computation with inverse-unit normalization and three-index reassociation.

lem-sfb-injective-finite-total-derived-comparison vs def-weil-pbc-etale-restricted-sections-lift: The existing definition constructs canonical lift through the monic filtered-step inclusion for a specified etale termwise hypercohomology presentation and truncation (or row comparison); it does not prove the K-injective finite-total computation with inverse-unit normalization and three-index reassociation.

lem-sfb-injective-finite-total-derived-comparison vs def-weil-pbc-etale-restricted-total-construction: The existing definition includes the underived finite-diagonal additive-functor total comparison and a truncated etale sections map s_q, but does not assert K-injective computation, inverse-unit normalization or the derived augmentation equation. That underived comparison is an ingredient of the K-injective finite-total computation with inverse-unit normalization and three-index reassociation.

lem-sfb-resolved-total-augmentation-square vs lem-sp-cartan-eilenberg-augmentation-quasi-iso: The existing statement proves that a supplied ordinary complex-to-total augmentation is a quasi-isomorphism from rowwise hypotheses; it neither constructs a strict diagram replacement nor treats its derived-unit comparison. The new statement concerns the normalized derived augmentation square for an arbitrary strict cosimplicial complex.

lem-sfb-resolved-total-augmentation-square vs lem-sp-cartan-eilenberg-total-resolution: The existing statement gives a K-injective total resolution of one complex; it does not assert the normalized derived augmentation square for an arbitrary strict cosimplicial complex.

lem-sfb-resolved-total-augmentation-square vs lem-sp-ce-acyclic-abutment: The existing statement concerns acyclic cartan--eilenberg total cohomology and image filtration for presentations attached to two composable functors F,G (with acyclicity hypotheses where stated), not the normalized derived augmentation square for an arbitrary strict cosimplicial complex for a general strict cosimplicial diagram.

lem-sfb-resolved-total-augmentation-square vs lem-sp-ce-acyclic-augmentation: The existing statement concerns natural acyclic cartan--eilenberg augmentation for presentations attached to two composable functors F,G (with acyclicity hypotheses where stated), not the normalized derived augmentation square for an arbitrary strict cosimplicial complex for a general strict cosimplicial diagram.

lem-sfb-resolved-total-augmentation-square vs lem-sp-ce-page-realization: The existing statement concerns functorial cartan--eilenberg page realization without acyclicity for presentations attached to two composable functors F,G (with acyclicity hypotheses where stated), not the normalized derived augmentation square for an arbitrary strict cosimplicial complex for a general strict cosimplicial diagram.

lem-sfb-resolved-total-augmentation-square vs lem-sp-ce-total-injective-terms: The existing statement gives only injectivity and the lower bound of total terms. This is one input to the new task, which additionally states the normalized derived augmentation square for an arbitrary strict cosimplicial complex.

lem-sfb-resolved-total-augmentation-square vs def-weil-pbc-ce-canonical-row-comparison: The existing definition constructs canonical normalized ce row comparison for a specified etale termwise hypercohomology presentation and truncation (or row comparison); it does not prove the normalized derived augmentation square for an arbitrary strict cosimplicial complex.

lem-sfb-resolved-total-augmentation-square vs def-weil-pbc-etale-filtered-step-cohomology-iso: The existing definition constructs canonical filtered-step derived-cohomology comparison for a specified etale termwise hypercohomology presentation and truncation (or row comparison); it does not prove the normalized derived augmentation square for an arbitrary strict cosimplicial complex.

lem-sfb-resolved-total-augmentation-square vs def-weil-pbc-etale-restricted-augmentation: The existing definition constructs explicit restricted augmented-total map for a specified etale termwise hypercohomology presentation and truncation (or row comparison); it does not prove the normalized derived augmentation square for an arbitrary strict cosimplicial complex.

lem-sfb-resolved-total-augmentation-square vs def-weil-pbc-etale-restricted-sections-lift: The existing definition constructs canonical lift through the monic filtered-step inclusion for a specified etale termwise hypercohomology presentation and truncation (or row comparison); it does not prove the normalized derived augmentation square for an arbitrary strict cosimplicial complex.

lem-sfb-resolved-total-augmentation-square vs def-weil-pbc-etale-restricted-total-construction: The existing definition includes the underived finite-diagonal additive-functor total comparison and a truncated etale sections map s_q, but does not assert K-injective computation, inverse-unit normalization or the derived augmentation equation. That underived comparison is an ingredient of the normalized derived augmentation square for an arbitrary strict cosimplicial complex.

## Allocation of the complete returned argument

The following are the EXACT eight returned step texts. They are planning material in this report, not proof steps or proof sketches inserted in the four unsplit nodes. Their constructions and conclusions are all assigned; the argument has not been discarded in order to meet the parent length bound.

### Former step 1 → lem-sfb-cosimplicial-injective-total-replacement

By [lem-weil-pbc-grothendieck-functorial-injective-embedding], $\mathcal A$ has functorial injective embeddings. Apply [lem-weil-pbc-functorial-bounded-injective-resolution] to obtain one functor $I$ on bounded-below complexes and a natural quasi-isomorphism $\eta_C:C\to I(C)$, preserving every strict lower bound. Put $J_n=I(K([n]))$ and $u_n=\eta_{K([n])}$. For every $\theta:[n]\to[m]$, set $J(\theta)=I(K(\theta))$. Functoriality retains every cosimplicial identity, and naturality of $\eta$ says $J(\theta)u_n=u_mK(\theta)$. Thus $u:K\to J$ is a strict map of cosimplicial complexes. Every $J_n$ is nonnegative with injective terms. The same construction applies simultaneously to an augmented diagram, including its augmentation object.

Source: {"document": "literature/stacks-project/derived.tex", "place": "Tag 0141, lemma-functorial-injective-resolutions (1) and remark-match; hypotheses supplied by injectives.tex, Tag 079H, theorem-injective-embedding-grothendieck"}

Existing ingredients: lem-weil-pbc-grothendieck-functorial-injective-embedding, lem-weil-pbc-functorial-bounded-injective-resolution.

### Former step 2 → lem-sfb-cosimplicial-injective-total-replacement

For $C=K,J$ form the first-quadrant double complex $D_C^{n,t}=C_n^t$ with first differential $\delta_C=\sum_i(-1)^i C(d^i)$ and second differential $d_C$. Paired cosimplicial identities cancel the summands of $\delta_C^2$; the cofaces are chain maps, so $d_C\delta_C=\delta_Cd_C$. Therefore [def-sp-double-complex-total] gives $T(C)$ with differential $\delta_C+(-1)^n d_C$. Naturality of $u$ makes $T(u):T(K)\to T(J)$ a chain map. For each fixed $n$, its internal-degree column map is the quasi-isomorphism $u_n$. That comparison asks for quasi-isomorphisms along the second index ($\mathrm{flip}.X\,n$), so apply [lem-sc-first-quadrant-total-column-comparison] to the transposed double complexes $D_C'^{t,n}=C_n^t$, with first differential $d_C$ and second differential $\delta_C$; its maps at fixed second index $n$ are the $u_n$. The maps $(-1)^{nt}$ on the summands $C_n^t$ give chain isomorphisms $\operatorname{Tot}(D_C')\cong T(C)$, natural in maps of double complexes: both differentials of $\operatorname{Tot}(D_C')$ on $C_n^t$, namely $d_C$ and $(-1)^t\delta_C$, become $(-1)^n d_C$ and $\delta_C$ after the sign. Hence $T(u)$ is a quasi-isomorphism. Both indices are nonnegative, as required by that comparison.

Source: {"document": "literature/stacks-project/homology.tex", "place": "Tag 0133, lemma-double-complex-gives-resolution and finite-diagonal comparison, applied to the map of first-quadrant complexes"}

Existing ingredients: def-sp-double-complex-total, lem-sc-first-quadrant-total-column-comparison.

### Former step 3 → lem-sfb-injective-finite-total-derived-comparison

For $r\ge0$, $T(J)^r=\bigoplus_{n=0}^r J_n^{r-n}$, and it is zero for $r<0$. This finite biproduct is injective: a map from the source of a monomorphism into it is a finite tuple of maps to the injective summands; extend each component across the monomorphism and combine them by the biproduct universal property. Thus [lem-sp-kinjective-computes] (2) makes $T(J)$ K-injective; it also makes every $J_n$ K-injective. Together with the preceding quasi-isomorphisms these are injective models of $T(K)$ and $K_n$. If an additional nonnegative resolution index $s$ is used while retaining original degree $q$, total degree $r$ has $n+q+s=r$; there are only finitely many such triples. Its differential has signs $\delta+(-1)^n d_q+(-1)^{n+q}d_s$, exactly those obtained by first totaling $(q,s)$ and then $n$. No infinite product or coproduct comparison is needed.

Source: {"document": "literature/stacks-project/derived.tex", "place": "Tag 070J, lemma-bounded-below-injectives-K-injective; Tag 015J, lemma-two-ss-complex-functor, proof remark (3) and finite total"}

Existing ingredients: def-sp-double-complex-total, lem-sp-kinjective-computes.

### Former step 4 → lem-sfb-injective-finite-total-derived-comparison

Let $\beta_J:F(T(J))\to T(FJ)$ be the degreewise finite-biproduct comparison. Its inverse is induced by the maps $F(\iota_{n,t})$ into $F(T(J)^r)$, where $\iota_{n,t}$ are the summand inclusions. The biproduct projection-inclusion identities prove that these maps are inverse. By [def-sp-left-exact-additive], $F$ preserves finite biproducts and addition, so $F(\delta_J)=\sum_i(-1)^iF(J(d^i))$ and $F((-1)^n d_J)=(-1)^nF(d_J)$. Checking each summand therefore proves that $\beta_J$ is a chain isomorphism. The same summand calculation proves $T(Fg)\beta_J=\beta_{J'}F(T(g))$ for every strict map $g:J\to J'$.

Source: {"document": "literature/stacks-project/derived.tex", "place": "Tag 015J, lemma-two-ss-complex-functor, proof: Tot(F(I)) = F(Tot(I)), with the finite-biproduct map and its naturality expanded"}

Existing ingredients: def-sp-left-exact-additive, def-sp-double-complex-total.

### Former step 5 → lem-sfb-injective-finite-total-derived-comparison

For a bounded-below injective complex $C$, write $\rho_C:RF(QC)\xrightarrow{\sim}QF(C)$ for the inverse of the right-derived unit on $C$. The specified-resolution comparison of [lem-sp-derived-injective-resolution-naturality] gives the normalized isomorphisms $c_{u_n}=\rho_{J_n}RF(Qu_n):RF(QK_n)\to QF(J_n)$, compatible with every cosimplicial operator. Define the coherent total on the right of the statement to be $QT(FJ)$ with these column identifications. Define
$$\chi_{F,K}=Q(\beta_J)\,\rho_{T(J)}\,RF(QT(u)).$$
All three factors are isomorphisms by the preceding steps and [lem-sp-kinjective-computes]. This is an isomorphism of entire derived objects. Its normalization uses the given augmentation $T(u)$ and the inverse derived unit, rather than choices of isomorphisms on cohomology.

Source: {"document": "literature/stacks-project/derived.tex", "place": "Tag 05TH, lemma-injective-acyclic; Tag 015J, lemma-two-ss-complex-functor, proof computing the whole derived object by the mapped total"}

Existing ingredients: lem-sp-derived-injective-resolution-naturality, lem-sp-kinjective-computes.

### Former step 6 → lem-sfb-resolved-total-comparison-descent

For a strict cosimplicial chain map $f:K\to L$, $g_n=I(f_n)$ gives a strict map $g:J_K\to J_L$ and $g u_K=u_L f$. Totalize this square. By [lem-sp-derived-injective-resolution-naturality],
$$QF(T(g))\,c_{T(u_K)}=c_{T(u_L)}\,RF(QT(f)).$$
Compose with the chain-isomorphism naturality $QT(Fg)Q\beta_{J_K}=Q\beta_{J_L}QF(T(g))$ from step 4. This gives $QT(Fg)\chi_{F,K}=\chi_{F,L}RF(QT(f))$. Identities and composites are respected because the chain-level maps, $F$, $I$, $T$, and $RF$ respect them. Columnwise the same naturality statement identifies $QF(g_n)$ with $RF(Qf_n)$. Thus the totalized map is the coherent derived-image map specified in the statement.

Source: {"document": "literature/stacks-project/derived.tex", "place": "Tag 0141, remark-match; naturality of the specified right-derived resolution comparison"}

Existing ingredients: lem-sp-derived-injective-resolution-naturality.

### Former step 7 → lem-sfb-resolved-total-comparison-descent

To compare any two compatible nonnegative termwise injective replacements $v:K\to L$ and $w:K\to M$, apply the fixed resolution functor $I$ to obtain the strict zigzag
$$L\xrightarrow{\eta_L}I(L)\xleftarrow{I(v)}I(K)\xrightarrow{I(w)}I(M)\xleftarrow{\eta_M}M.$$
Every arrow is a columnwise quasi-isomorphism: this is true of $\eta$, and follows for $I(v),I(w)$ from $I(v)\eta_K=\eta_L v$ and its analogue by two-out-of-three. All columns are bounded below and termwise injective, so [lem-sp-kinjective-computes] (1) makes these column maps homotopy equivalences; additive $F$ preserves a homotopy inverse and its homotopies. Apply [lem-sc-first-quadrant-total-column-comparison] in $\mathcal B$, through the sign-$(-1)^{nt}$ transposition of step 2, to see that all arrows of the zigzag of $T(F(-))$ are quasi-isomorphisms. Naturality of $\eta$ makes each leg commute with its augmentation from $K$; after totalization, [lem-sp-derived-injective-resolution-naturality] identifies each leg with the corresponding normalized comparison from $RF(QT(K))$. Hence this zigzag identifies the two displayed $\chi$ maps. Any other zigzag commuting with the augmentations has the same identification, since it must equal $\chi_M\chi_L^{-1}$. This proves independence and its compatibility with the naturality equation of step 6.

Source: {"document": "literature/stacks-project/derived.tex", "place": "Tag 0141, lemma-functorial-injective-resolutions and remark-match; common functorial-resolution zigzag, with normalized comparison by the derived unit"}

Existing ingredients: lem-weil-pbc-functorial-bounded-injective-resolution, lem-sp-kinjective-computes, lem-sc-first-quadrant-total-column-comparison, lem-sp-derived-injective-resolution-naturality.

### Former step 8 → lem-sfb-resolved-total-augmentation-square

Let $b:\operatorname{const}(A)\to K$ be the strict augmentation. Resolve the entire augmented diagram by $I$: its augmentation is $I(b):\operatorname{const}(I(A))\to J$, and $u_n b_n=I(b_n)\eta_A$. Define $b_J:I(A)\to T(J)$ by $I(b_0)$ into cosimplicial degree zero and zero in other cosimplicial degrees. The augmentation identities give $J(d^0)I(b_0)=J(d^1)I(b_0)$, so its coface differential is zero. It is therefore a chain map and $b_J\eta_A=T(u)a$. By [lem-sp-derived-injective-resolution-naturality] this square gives
$$QF(b_J)c_{\eta_A}=c_{T(u)}RF(Qa).$$
Under $\beta_J$, $F(b_J)$ is the map with $F(I(b_0))$ in cosimplicial degree zero and zero elsewhere, by its summand definition. This is exactly the totalized derived augmentation, since the column comparisons identify $F(I(b_n))$ with $RF(Qb_n)$. Therefore $\chi_{F,K}RF(Qa)$ equals that augmentation. For a map of augmented diagrams the equalities $f_n b_n=b'_n h$ remain equalities after $I$ and $F$; in degree zero they give the total augmentation square, and in higher cosimplicial degrees both augmentation components are zero. Steps 6 and 7 transport this square through all normalized comparisons and resolution changes.

Source: {"document": "literature/stacks-project/derived.tex", "place": "Tag 0141, diagramwise natural resolution including the augmentation object; naturality of the inverse derived unit; Tag 015J finite total calculation"}

Existing ingredients: lem-weil-pbc-functorial-bounded-injective-resolution, lem-sp-derived-injective-resolution-naturality, def-sp-double-complex-total.

## Remaining work and verification

All four new tasks intentionally remain unsplit for parallel stage-1 work; no claim that their Lean proofs are finished is made. The parent one-level repair is complete. The server-only check_dag and review_split calls passed before report packaging. The first full deliver.py dry run passed at 4f29dd1edd8 after adding its requested same-tag comparisons. A final explicit intermediate-replacement hypothesis is being rechecked by a second dry run. The final dry run and push results are reported by the delivery command; no compiler or Lake tool is run in this stage.
