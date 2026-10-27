## Worker report

Stage 2 continuation, Q20. The resumed prompt and coord/queue.tsv identify stage 2; coord/brief-stage2.md §0 explicitly explains this handoff from an unchanged-item stage-1 attempt. The former stage-1 delivery process no longer has a live tool session, left no ready receipt, and never pushed. Its stale-assignment report is superseded by this stage-2 statement delivery. The accepted five-step split and its mathematical statement are unchanged.

Files: lean/Sheaf/AlgebraicGeometry/ReducedSingletonFieldFactorization.lean and the item node, plus this report. One theorem, AlgebraicGeometry.AlgebraicSpace.existsUnique_factor_through_field_of_reduced_singleton_image, with a sorry proof. No definitions, new nodes, dependency modules, or attachments. Only lean and two added landed stmt_deps differ in the item.

Hypothesis and conclusion correspondence:

- `S : Scheme.{u}` and `X Y : AlgebraicSpace S` are the base and algebraic spaces. `F : Type u` has `[Field F]`; `s : Spec (CommRingCat.of F) ⟶ S` supplies the spectrum's S-structure.
- `j : yoneda.obj (Over.mk s) ⟶ X.obj.obj` is the given S-morphism. `[Mono j]` is injectivity of composition. This ambient presheaf monomorphism is equivalent to the stated monomorphism on algebraic spaces: representable scheme tests are algebraic spaces, so their cancellation detects pointwise injectivity, which then implies cancellation against every presheaf.
- `hqc : MapIsQuasiCompact j` uses the existing affine scheme-test compactness of pullback point spaces. It agrees with the node's quasi-compactness on all quasi-compact opens by a finite affine cover. No representability assumption is added: the representable diagonal of X already makes a scheme-source map representable.
- `hred : IsReduced Y` uses the existing algebraic-space reducedness predicate. Every etale scheme chart is reduced, equivalently affine section rings on an etale atlas are reduced, by etale locality. This is precisely the node's notion, not a second predicate.
- `f : Y ⟶ X` is the map in the assertion. `pointImage f.hom.hom` uses the recorded field-valued point image. `schemePointMap j (IsLocalRing.closedPoint F)` names x as the image of the unique point of Spec F; the singleton inclusion is exactly the point-image hypothesis without an arbitrary choice or additional condition.
- `∃! g : Y.obj.obj ⟶ yoneda.obj (Over.mk s), g ≫ j = f.hom.hom` is existence and uniqueness of the S-morphism Y → Spec F whose composite with j is f. Maps of algebraic spaces are natural transformations, and every transformation here is on Over S, so the S-structure is enforced.

Dependency interfaces read: AlgebraicSpace.lean (AlgebraicSpace, its full-subcategory morphisms and representable etale atlas); AlgebraicSpacePointClasses.lean (PointRepresentative, Point and schemePointMap); AlgebraicSpacePointTopology.lean (pointImage and final topology); ReducedAlgebraicSpace.lean (IsReduced); ProperCurveModuli.lean lines 40–58 (mapPoint and MapIsQuasiCompact). Mathlib Scheme/ResidueField supplies Spec and the field spectrum's unique point. Added landed dependencies: def-sfb-reduced-algebraic-space and def-sfb-proper-curve-moduli, both with usable records owning the exact definitions used. Neither definition node is edited.

The module imports the stated proof inputs AlgebraicSpaceAffineEtaleCover, AlgebraicSpaceEtaleOpenImage, AlgebraicSpaceFibreProductsEtaleCovers, the general reduced-source closed-immersion factorization, and relevant Mathlib modules. No module is yet available for lem-a1-space-open-factor-scheme-tests, lem-a1-space-point-open-calculus, lem-sfb-monomorphism-into-field-coproduct, lem-sfb-qc-space-schematic-strata or lem-sfb-reduced-scheme-single-point-residue-factorization; these are future proof inputs, not prerequisites for this statement. The docstring preserves all five accepted proof steps.

Source read: decent-spaces.tex, Tag 0H1T (lemma-factor-through-residual-space-decent), full statement and proof, including its use of 0H1R for the identification of the residual space. No Noetherian, quasi-separatedness or closed-point hypothesis is added. No SGA route is used.

Edge cases checked: empty Y has empty point image and the unique map to Spec F; the field is nonzero, so its canonical spectrum point exists. If X = Spec F and j is the identity, the factorization is f. Generic points are permitted: x need not be closed in X. Nonreduced sources are excluded as required (Spec k[ε]/(ε²) mapping to A¹ by t ↦ ε illustrates the need). The site uses universe u consistently for schemes and fields, with point classes in u+1, without a smaller independent test universe or finiteness assumption on Y.

Searches for an existing statement, actually run through msearch.py:

- grep: `factor.*[Rr]esidu|[Rr]esidu.*factor|[Aa]lgebraic[Ss]pace`. Available; 1 hits. Candidates: Mathlib/AlgebraicGeometry/ValuativeCriterion.lean. No match for algebraic-space factorization; residue-field scheme statements supply only proof inputs.
- leansearch: `A reduced algebraic space with singleton image factors uniquely through a quasi compact monomorphism from the spectrum of a field`. Available; 8 hits. Candidates: AlgebraicGeometry.IsReduced.mk, AlgebraicGeometry.instIsAffineOfSubsingletonCarrierCarrierCommRingCat, Algebra.QuasiFinite.iff_finite_comap_preimage_singleton, AlgebraicGeometry.isFinite_iff_locallyOfFiniteType_of_jacobsonSpace, AlgebraicGeometry.Scheme.instUniqueCarrierCarrierCommRingCatSpecOf, AlgebraicGeometry.Scheme.range_fromSpecResidueField, Algebra.QuasiFinite.isDiscrete_comap_preimage_singleton, AlgebraicGeometry.QuasiCompact.isCompact_preimage_singleton. No match for algebraic-space factorization; residue-field scheme statements supply only proof inputs.
- loogle: `AlgebraicGeometry.IsReduced, AlgebraicGeometry.Scheme.SpecToEquivOfField`. Available; 0 hits. Candidates: none. No match for algebraic-space factorization; residue-field scheme statements supply only proof inputs.
- leanfinder: `A reduced scheme mapping to just one point factors through its residue field, and the analogue for a quasi compact field monomorphism into an algebraic space`. Available; 8 hits. Candidates: AlgebraicGeometry.Scheme.over_def, AlgebraicGeometry.Scheme.SpecToEquivOfField, AlgebraicGeometry.Scheme.instIsPreimmersionFromSpecResidueField, AlgebraicGeometry.Scheme.instIsOverMapResidueFieldMapOverInferInstanceOverClass, AlgebraicGeometry.Scheme.fromSpecResidueField, AlgebraicGeometry.Scheme.instIsPreimmersionMapResidue, AlgebraicGeometry.Scheme.instOverSpecResidueField, AlgebraicGeometry.Scheme.instCanonicallyOverSpecResidueField. No match for algebraic-space factorization; residue-field scheme statements supply only proof inputs.

Project searches for the exact blueprint tag and for factor/residue, reduced/singleton and field/monomorphism in lean/WeilConjectures and lean/Sheaf found no exact algebraic-space theorem. Scheme.SpecToEquivOfField and range_fromSpecResidueField were read in Mathlib/AlgebraicGeometry/ResidueField.lean: they concern scheme field-valued maps, not the reduced algebraic-space assertion. Existing ReducedAlgebraicSpace and ProperCurveModuli definitions are reused; no notion is duplicated.

Validation: batch2/scompile.py exited 0. The server checked both sandbox and library module modes cleanly (16.2 s and 7.7 s). All lines are at most 100 characters. Stage-2 delivery preflight is next; no local compiler or global build was run.

WANTED: none. Statement disputes: none. Unfinished: the intended stage-2 sorry proof only.

## Review by Q20

I matched the unchanged DAG assertion and the source to every binder and conclusion of the Lean signature, then read the definitions actually used. The delicate choices were the presheaf monomorphism, affine-test quasi-compactness and all-etale-chart reducedness; their equivalence to the node's conventions is explained above. The canonical closedPoint is a point of the field spectrum and does not require x closed in X. The existential includes uniqueness and the exact composite equation, with all maps over S. The docstring follows the five accepted steps; no proof was attempted. No correction was necessary. This is the author's check under direct delivery; the maintainer supplies the independent review.

## Second reading by Q20

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
