## What changed

Completed the two proofs in `Sheaf.Paper.InternalScalarMateTransitivity`, keeping all
existing public declaration signatures, definitions and attributes.
The scalar compositor is constructed by uniqueness of left adjoints after the fixed
exact-restriction compositor. Its computation-counit normalization follows from the
derived-adjunction unit factorization and normalized adjunction composition.

The ordinary geometric rectangle is proved by conjugating to restriction functors,
whose underlying module maps are identities. Computation-counit naturality transports
this rectangle to the derived functors. K-flat resolutions for scalar extension
and exactness of geometric pullback give the required uniqueness. Direct-image pasting
then follows by transposing with the specified geometric adjunctions. The same argument
handles identity coefficients and both identity factors in a scalar tower.

Added only proved private helpers. General categorical unit, transpose, mate-rectangle
and absolute uniqueness calculations are proved before specializing to internal modules;
this avoids repeated expansion of the concrete adjunction constructions.
The new private proof imports are
`WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates` and
`Sheaf.CategoryTheory.DerivedCategory.NormalizedAdjunctionComposition`.
Updated the attached node's proof, proof dependencies, proof origin and obsolete tool uses.
No consumer adaptation or definition repair is required. Local unfolding controls prevent
repeated expansion; the ordinary restriction rectangles use explicit rewrite lists.
The unused generated reassociation lemma has been removed. The blueprint unit's statement
and steps are preserved.

## Proved and sorry left

Closed both original holes:

- `AlgebraicGeometry.ProEtale.QuotientChange.internal_scalar_mate_transitivity`.
- `AlgebraicGeometry.ProEtale.QuotientChange.internal_scalar_identity_normalization`.

The item has zero `sorry` occurrences. No holes or new statements with `sorry` are added
elsewhere; zero statements are split off. Existing imported results remain the inputs
of this stage-3 proof.

## No longer needed

Removed these private proof imports and their use in this node's argument:

- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`,
  node `lem-sfb-successive-derived-quotient-normalization`: ordinary and derived
  adjunction uniqueness construct and normalize the scalar compositor directly.
- `Sheaf.Algebra.Homology.RingedKFlatWordComparisonDescent`,
  node `lem-trf-ringed-kflat-word-comparison-descent`: counit naturality and the absolute
  left-derived universal property prove coherence without a simultaneous word resolution.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`,
  node `lem-pur-sheaf-ring-derived-coefficient-adjunction`: the specified internal scalar
  adjunction and its generic derived unit factorization suffice.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`, used for the planned tensor calculation:
  the ordinary rectangle is proved by conjugation and module-map extensionality.

Also removed `def-pur-sheaf-tensor-product` and `lem-weil-pbc-mate-pasting` from the proof
and tool dependencies. No tensor-generator calculation is used, and the direct-image
identity is proved directly with the mate-counit formula and naturality.

Removed the unused public imports `Sheaf.Topology.ProfiniteCondensedRing` and
`Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`. The former's presentation of
condensed rings contributes no declaration to this proof. The latter's ordinary-ring
presentation theorem and node `lem-pur-derived-change-of-rings` are not proof inputs:
the internal K-flat derived-functor API is already supplied by
`InternalDerivedScalarComparisons`. The node remains a statement dependency.

Removed the unused public import `Sheaf.Paper.InternalScalarPullbackNormalization`.
This item takes the three normalized balancing maps as hypotheses; it does not invoke
`internal_scalar_pullback_normalization` or the section-model data. Its node remains a
statement dependency, reflecting the origin of those hypotheses. The pruning above
concerns this item's proof route; no source declaration or module is withdrawn.
There are no current Lean importers of this item, and none require adaptation.

## Where the brief, the DAG or earlier work was wrong

No statement was found false or changed. The DAG's section-ring passage and K-flat word
resolution are unnecessary for these coherence statements. The library already provides
canonical adjunctions, exact restriction comparisons, and absolute left derivability.
Using these gives the same normalized maps and proves their compatibility directly.

Validation: both public theorem statements and all three original public definition
bodies are unchanged. Import-direction checks passed for both added private imports.
Both original holes are closed without adding holes. The complete proof with the
standard delivery axiom probe passed on the project server in 48.0 seconds
(`SHEAF-PROBED 12`). Late homotopy and derived comparison constructors and the mate
are kept locally irreducible after their computation lemmas. Generic module restriction
rectangles avoid expansion of concrete
sheaf comparisons. Uniqueness after postcomposition follows by taking a K-flat left
resolution, cancelling its invertible computation counit, and transporting equality
along the localized resolution isomorphism. The scalar interface is unfolded explicitly
only at this specialization. Earlier failed delivery attempts pushed nothing.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
