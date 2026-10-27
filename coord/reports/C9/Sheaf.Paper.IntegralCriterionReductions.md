## What changed

Proved `integralSectionRingIso_existsUnique` by lifting the fixed monoidal abelian comparison to section rings and using faithfulness for uniqueness. Replaced the hole in `AlgebraicGeometry.ProEtale.continuousIntegralConstructible_iff_sfIntegralConstructible` by the assembly of coefficient restriction squares, their unit-compatible derived mates, reflection of the reduction Roos triangle, finite-coefficient constructibility, and the elementary equivalence between a support interval and vanishing outside that interval. The original statements, canonical ring comparison, public imports, and unit route are unchanged.

The new modules isolate two independent missing results from the coefficient-comparison and derived-completion arguments: the finite quotient projection equation for the *specified* normalized integral ring comparison, and completeness of the actual internal quotient Roos output. The restriction-square construction is assembled generically over abstract ring sheaves, including the recorded encoding transports, to avoid unfolding completed coefficients. It and the implication from a distinguished internal Roos triangle to completeness are proved from those results. Their source references and complete proof plans are in their docstrings and DAG nodes. All new imports in the item are private proof imports.

The finite normalized encodings used by the existing model-comparison theorem need not equal the ones in the restriction squares as structures. The proof establishes uniqueness of their normalized ring isomorphisms by sheafification, obtains a natural isomorphism of their functors, and transports bounded constructibility through its localization. Exact equivalences preserve homology and zero objects; finite support follows from containment in the same finite integer interval.

## Proved and sorry left

Current item baseline: three holes, in
`AlgebraicGeometry.ProEtale.integralSectionRingIso_existsUnique`,
`AlgebraicGeometry.ProEtale.continuousIntegralConstructible_iff_sfIntegralConstructible`, and
`AlgebraicGeometry.ProEtale.integral_reductions_constructible_iff`.
The ring-isomorphism theorem is proved from existing declarations. The continuous/sectionwise
criterion is decomposed through the two independent results below. The first-reduction
theorem `AlgebraicGeometry.ProEtale.integral_reductions_constructible_iff` retains its
original hole and proof plan. The packet closes two upper holes and adds two lower holes;
the item has one remaining `sorry`. This is a decomposition, not a net decrease in holes.

New holes:

- `AlgebraicGeometry.ProEtale.IntegralPresentation.integral_section_projection_normalization` in `Sheaf.SixFunctors.ProEtale.IntegralSectionProjectionNormalization`, node `lem-pe-integral-section-projection-normalization`.
- `AlgebraicGeometry.ProEtale.AdicCompletion.isDerivedComplete_roos` in `Sheaf.SixFunctors.ProEtale.InternalRoosOutputComplete`, node `lem-pe-internal-roos-output-complete`.

The new declarations `fixed_integral_section_squares` and `isDerivedComplete_of_roos` are proved from the two listed results and existing declarations. The latter uses rotated distinguished triangles and reflects their third-vertex isomorphism through the shift equivalence.

Both retained holes omit all constructibility, Noetherian, and uniform-bound hypotheses of the criterion. The first is solely a coefficient normalization result. The second is solely the regular-scalar output-completeness argument for the actual Roos construction. Neither restates the target under another name. The existing final theorem combining the first-reduction criterion with completeness is retained verbatim and still depends on the original first-reduction hole.

## No longer needed

No existing module or declaration is withdrawn. The original induction dependencies
remain in the DAG because `integral_reductions_constructible_iff` is unfinished.
All original public imports are unchanged. No source-library declaration is changed.
An attempted private import of `Sheaf.Paper.SuccessiveReductionConstructibility` was
removed: its unpublished source and DAG node are absent from the shared repository,
although an earlier compiler run supplied an unpublished overlay. The packet does not
rely on that overlay or claim its induction as proved.

## Where the brief, the DAG or earlier work was wrong

The last DAG step invokes `integral_completion_presentation` on an already complete object. That theorem proves only forward completeness. The existing public criterion is an equivalence for arbitrary `K`, so its reverse implication also needs the canonical-map completeness argument; a generic isomorphism between vertices of two Roos triangles does not show that the specified augmentation is invertible.

The existing normalized restriction-square theorem existentially chooses the integral encoding. The item instead fixes its ring isomorphism by `SfbIntegralComparison`. The existential theorem does not assert that its chosen encoding has that normalization, so it cannot simply be applied to the item's prescribed equivalence. The new coefficient lemma states the needed finite projection equation with both endpoint equalities. The restriction-square theorem constructs its identity on underlying sections from that equation.

## New nodes

`lem-pe-fixed-integral-section-squares`: proved construction of positive finite restriction squares from the coefficient projection equation, the actual section restriction isomorphism and association of restriction of scalars. Tested conceptually at exponent one, the zero module, and the empty scheme: all maps retain the same section identities and require no nonempty object or stratum. The statement uses the full mate-and-projection normalization, not an arbitrary ring isomorphism.

`lem-pe-integral-section-projection-normalization`: the missing equation of reconstructed coefficient ring maps. It is independent of module and derived-category arguments; the proof plan uses the actual point adjunction and the specified finite-label normalization.

`lem-pe-internal-roos-completeness`: proved implication from a distinguished quotient Roos triangle using output completeness and isomorphism invariance of the existential representative definition. The regular uniformizer hypothesis comes from the fixed coefficient DVR, not an extra hypothesis on `K`. Zero objects and unbounded objects are included. An object on which the uniformizer is invertible has zero reductions, and the assumed distinguished triangle then forces it to be zero, as the conclusion requires.

`lem-pe-internal-roos-output-complete`: the independent output-completeness assertion for the actual strict Roos complex of a K-flat input. Its source is the regular Koszul completion reflector, with section/tensor and representative comparisons recorded in the proof plan. It does not restate either constructibility implication.

No definition or existing statement is changed, so there is no change record or forced consumer adaptation.

The output-completeness proof plan uses the ringed Koszul completion reflector
`lem-weil-pbc-ringed-koszul-completion-reflector` as an algebraic tool: it supplies
output completeness and the normalized unit criterion, with no proper-base-change
conclusion. The existing regular quotient/Koszul comparison already uses this reflector.
Representative transport cites `lem-pe-kflat-roos-representative-invariance` explicitly.

Validation: the two new glue modules compile, and the item compiles against them.
The retained first-reduction hole is the original named theorem, not a new split.

## Second reading by C9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
