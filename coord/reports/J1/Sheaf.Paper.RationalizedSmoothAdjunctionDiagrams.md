## What changed

Change `lean/Sheaf/Paper/RationalizedSmoothAdjunctionDiagrams.lean` and the proof
record of `lem-pur-rationalized-smooth-adjunction-diagrams`.
The existing theorem statements, instances, public imports and docstrings are
preserved. `Raw`, `IntegralComparisons` and `RationalComparisons` now
specialize generic records with exactly their original fields. This avoids
generating record machinery over the full scheme and padic coefficient expressions.
The `Raw` unit and counit right sides are tensors with one, definitionally the
maps of the same integral localization functor. The comparison predicates are
copied verbatim from the original records. No mathematical data or compatibility
equation is dropped. Six theorem bodies now have proofs:

- Assemble the supplied tower purity naturality and source comparison into a
  natural transformation, conjugate through the fixed realization equivalence,
  and apply the reconstruction unit and total-limit functor. These are exactly
  the existing `gammaComponent` components. The supplied `purity_realization`
  field proves their invertibility in the full subcategory.
- Deduce invertibility of `gammaTransformation` componentwise.
- A proved private helper upgrades an adjunction Hom equivalence to a linear
  equivalence, using `homAddEquiv`, the unit formula, and scalar bilinearity.
  Apply it to the smooth adjunction and to the tower adjunction; obtain the
  tower right adjoint's linearity from the existing linear-right-adjoint theorem.
- Construct the raw localized adjunction directly from the integral unit and
  counit tensored with one. The existing semilinear Hom-extension theorem and
  uniqueness of the coefficient map give the pure-tensor functor formula.
  Generic helpers use the actual additive Hom extension on tensor modules,
  avoiding repeated unfolding of the scheme-level functors. Tensor induction
  proves both naturality equations; the integral triangle
  identities give the rational triangles. Keep this private construction
  irreducible, with proved unit, counit and Hom-formula lemmas, so the scheme-level
  proof does not repeatedly unfold its tensor-induction proofs. Compute both Hom
  directions on pure tensors, and prove the additive and scalar laws from this adjunction.
- For realization agreement, tensor induction identifies `tensorHom` with the
  arbitrary supplied `Raw.adjunction.homEquiv`. The pure-tensor case uses the
  chosen integral equivalence's specified equality; zero and sums use the
  recorded scalar and additive laws. Cancel the two endpoint comparisons and
  the inverse Hom comparison in `threeHom`.

Add the proof import `Mathlib.CategoryTheory.Adjunction.Additive`, and
`import all` of `Mathlib.Logic.Small.Defs` and
`Mathlib.CategoryTheory.Limits.HasLimits`. These make the existing `Shrink`,
`equivShrink`, and limit/colimit-choice definitions visible for conversions in
the encoded Hom and reconstruction types. No new theorem statement or
dependency module is introduced. The three generic records and their specialized abbreviations
are the public definition changes.
The original unit route stays unchanged. Update only the existing node's proof
and proof origin to record the direct construction by localized unit and counit
before identifying its Hom bijections with the tensor equivalence.

Validation: the complete file compiled without warnings or errors through
`lcompile.py` in 56.0 seconds, under the 60-second limit.

## Proved and sorry left

The module originally had nine holes. Close six, by full declaration name:

- `WeilConjectures.RationalizedSmoothAdjunction.gamma_laws`
- `WeilConjectures.RationalizedSmoothAdjunction.gammaTransformation_isIso`
- `WeilConjectures.RationalizedSmoothAdjunction.hom_linear`
- `WeilConjectures.RationalizedSmoothAdjunction.tower_hom_linear`
- `WeilConjectures.RationalizedSmoothAdjunction.raw_exists`
- `WeilConjectures.RationalizedSmoothAdjunction.realization_agreement`

Three original holes remain, each with its original source and proof docstring
and the existing node `lem-pur-rationalized-smooth-adjunction-diagrams`:

- `WeilConjectures.RationalizedSmoothAdjunction.integral_linear`
- `WeilConjectures.RationalizedSmoothAdjunction.coefficient_comparisons`
- `WeilConjectures.RationalizedSmoothAdjunction.rationalized_smooth_adjunction_diagrams`

No holes added or split off. This is a partial delivery of the module's clauses.
The linear Hom and raw-localization proofs use the existing still-open
`integral_linear` declaration, as intended by stage 3; they do not establish its
compact-support linearity clause.

## No longer needed

Remove three unused proof imports from this module:

- `Sheaf.CategoryTheory.KInjectiveTotalDerivedLinear`
- `Sheaf.Algebra.Homology.OrdinaryLineDerivedScalarComparison`
- `Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints`

No entire node or module is claimed pruned: these results remain in the plan
for the original unfinished clauses, and other modules may still import them.
All original public imports are preserved. No blueprint unit is bypassed.
The scheme-specific generated auxiliary declarations of the three old records
are replaced by the generic record machinery; no source uses their qualified
names. No corresponding DAG node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement or source correction. The public definition changes
are representation repairs of the three expensive indexed records, with every
field retained. The traced run identifies the original structures and their
generated machinery as substantial kernel and elaboration costs. The source-only
downstream check reports no importing module, so no consumer adaptation is needed.
See `coord/changes/J1-rationalized-smooth-adjunction-records.md`.
The existing purity package already supplies both the tower naturality law and
invertibility of the realized component, so `gamma_laws` needs only composition
of the specified natural transformations. The realization equality needs only
the laws already recorded in `Raw`, for arbitrary endpoint and Hom comparisons
of the given types.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
