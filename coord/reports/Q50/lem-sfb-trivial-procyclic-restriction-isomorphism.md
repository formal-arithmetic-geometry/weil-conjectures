# Stage-1 report: lem-sfb-trivial-procyclic-restriction-isomorphism

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-trivial-procyclic-restriction-isomorphism.json: statement; split using existing nodes; not a Mathlib leaf.
- citations.json: verbatim statement excerpts for all ten step/node incidences.
- report.md: this report.

New nodes: 0. New Mathlib leaves: 0. The six steps are each shorter than 2000 characters.

## Attachments

None. The exact blueprint tag is absent from lean/WeilConjectures, and searches for procyclic restriction and condensed bar computations found no declaration giving this statement. I read WeilConjectures/RepresentationTheory/DiscreteModule/Procyclic.lean lines 617–678: its HZeroPadicIntAddEquiv, HOnePadicIntAddEquiv and subsingleton_H_padicInt concern discrete continuous modules (and primary torsion for higher degrees). They do not give ordinary internal modules over the norm-continuous scalar ring, nor the specified augmentation or normalization. No attachment is asserted.

## Wanted references

WANTED: an external reference for the ordinary internal condensed norm-scalar bar augmentation and procyclic comparison, including incomplete algebraic-closure scalars, for lem-sfb-trivial-procyclic-restriction-isomorphism. Existing analytic nodes already isolate these obligations. Stacks Tag 0DVG defines the continuous differential only; it is not cited as proving the condensed comparison. No missing document was downloaded.

## Findings and changes

The imported item was statement-only. Its statement is retained verbatim, including full ordinary action categories, all continuous functions, the noncomplete field Omega, actual map normalization and the zero-dimensional case. There is no statement dispute.

I read the latest blueprint through literature/blueprint/latest (main-20261023-1620), paragraph (3) of sk-thm-sf-ctf-stability-direct-images.proof.md. Its open direct image uses sk-prop-open-coefficients; this item is an existing auxiliary analytic obligation below that route, not a theorem stated verbatim by the blueprint. The chapter and the unit records were read; their historical source paths and the null ancestor returned by blueprint_refs.py were retained. Whole-blueprint searches for procyclic, cyclic restriction and biproduct supplied no equal statement. In particular the discrete primary-torsion blueprint lemma is different.

No new nodes were necessary: creating another scalar evaluation, scalar bar augmentation or normalized cyclic comparison would duplicate existing nodes. The finite-dimensional passage is written directly using the stipulated product topology and explicit finite-coordinate maps. The only off-unit proof tool is lem-sc-first-quadrant-total-column-comparison; split_report.tool_uses explains its role.

The five required Mathlib queries ran through msearch.py and their exact records are copied from searches.jsonl. Both natural-language phrasings were read. Representation.invariants_eq_top and Rep.invariantsAdjunction concern abstract representations. Condensed.profiniteFree defines a free condensed module and supplies no invariant computation. groupCohomology.inhomogeneousCochainsIso and Rep.standardComplex resolution results concern abstract group representations; ContinuousCohomology.continuousCohomologyZeroIso is only degree zero in topological modules. None states the current theorem. I read the relevant local RepresentationTheory/Invariants.lean, Condensed/Solid.lean and GroupCohomology/Basic.lean; the search service's ContinuousCohomology/Basic.lean path does not exist in the pinned local Mathlib, further preventing use of that remote result as a local match. No search was invented and no unavailable service was reported as absence.

## Unfinished work

No unresolved assembly step remains. The existing cited analytic nodes remain separate DAG obligations; this delivery does not claim they have Lean proofs. Required server dry run and delivery results are recorded below when complete.

## Not duplicates

No new nodes were created, so there are no new/existing-node pairs to distinguish.

## Review by Q50

I checked the split against delivery-errors B–E with the cited node statements open. Every object is introduced in the unchanged item, no statement-only node contains a proof, and there are no new nodes hiding a clause of the item. I read Stacks etale-cohomology.tex at section-continuous-group-cohomology (0DVG), including its warning that topological cohomology alone does not identify derived functors; I also read homology.tex at lemma-first-quadrant-ss and lemma-double-complex-gives-resolution. The main assembly is explicitly marked agent-written, because the blueprint and these passages do not themselves prove the analytic inputs. No SGA source is used.

Step 1 uses the entire sheaf quasi-isomorphism assertion of lem-sfb-procyclic-scalar-cochain-evaluation with precisely the same E/Omega alternatives, profinite parameters and unclosed kernel/image cohomology. The localization clause of def-weil-abstract-derived-category then makes its map invertible. This does not replace local primitives by global primitives.

Step 2 uses lem-sfb-condensed-derived-invariant-bar for one compatible nonnegative derived-bar model and lem-sfb-normed-scalar-profinite-hom-acyclic for its actual evaluation-normalized column maps. I checked that the latter assumes F=E finite, and apply it only there, with P=H^q profinite for every nonnegative q (including the singleton at q=0). The double complexes are first quadrant; a degree-n diagonal has n+1 terms. These are exactly the hypotheses of lem-sc-first-quadrant-total-column-comparison, whose statement gives the actual total map as a quasi-isomorphism. I did not infer total quasi-isomorphism from an objectwise comparison without a cited total-comparison theorem.

Step 3 uses lem-sfb-norm-algcl-bar-augmentation exactly for Omega. I compared its underived function sheaves, full action injective resolution, augmentation map and derived target with the item. It states invertibility of the actual morphism, not just existence of an isomorphism between its endpoints. Its statement explicitly avoids a termwise acyclicity or completeness assertion. The evaluated-only augmentation node would not suffice here and is not cited.

Step 4 uses the final displayed identity in lem-sfb-relative-cyclic-restriction-model, which explicitly includes the underived-to-derived augmentation j and evaluation at u(1); the residual group is 1 and u(1)=1. The bar node states eta is an isomorphism. Solving that displayed equality gives the explicit composite formula for c_A, so no normalization or restriction compatibility is silently inferred from H^0 or H^1 alone.

Step 5 is an elementary finite-coordinate argument, not an analytic lemma: the tensor extension is given the product norm topology in the item itself. Its coordinates and inverse are the finite-basis tensor formulas. A map into that finite product is continuous if and only if all coordinates are continuous. This supplies sectionwise A-linearity and naturality, and hence the internal module isomorphism. No general norm-equivalence theorem or completeness of Omega is used. For W=0, the empty tuple is the unique element of the zero module; the same interpretation works for S empty.

Step 6 cites lem-sfb-condensed-action-injective-infrastructure for additive total derived invariants and lem-sfb-relative-cyclic-restriction-model for the natural canonical comparison. I checked that these statements concern ordinary internal full action categories, not discrete modules. Instead of assuming injective resolutions commute with arbitrary sums, the step writes a finite sum of inclusion/projection maps giving an inverse and verifies both composites using naturality. This is valid for every finite d and for the empty sum: the identity of a zero object is zero. The chosen coordinates prove invertibility of the canonical map and do not redefine it.

Finally, I traversed statement and proof dependencies below each principal input: none reaches this item, so the citations create no cycle. Every proof use is listed in proof_deps; citations.json contains a literal excerpt of its node statement for every use. The only elementary step is the explicit product-coordinate identification. There are no long steps hiding additional analytic or comparison lemmas.

## Validation

The first dry run caught two excerpts shorter than the citation checker minimum. I expanded the cyclic identity and additivity excerpts to include their complete assertions, and also expanded the bar-isomorphism and natural-comparison excerpts so that the recorded quotes exhibit the actual facts used. The mathematical split did not change.
