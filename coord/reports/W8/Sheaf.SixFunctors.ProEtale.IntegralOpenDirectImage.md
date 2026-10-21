## What changed

Replaced the proof of `AlgebraicGeometry.ProEtale.IntegralOpenDirectImage.integral_open_direct_image`
without changing its signature or `reductionPullbackMap`. The proof constructs the comparison
by the actual geometric adjunction Hom bijection and proves its defining equation and
uniqueness by cancellation. Private helpers prove that the actual residue quotient is
finite, discrete and killed by l, and apply the existing
`finiteOpenDirectImage_constantModel_torAmplitude` to prove the finite-residue step.
Isomorphism invariance transports this result across the specified comparison.
No existing definition, public import, or adopted-source declaration changes.

Two separate source arguments are stated in new modules: the integral-models residue
criterion in the actual internal continuous presentation, and the general direct-image
finite-projection/completion theorem in that presentation. Each has its source, proof in
words, new node and explicit dependencies. They are independent of open immersions and of
the geometry of a finite-type scheme over k; neither restates the assigned theorem.
The item's node now follows these arguments and the existing finite-coefficient theorem.

## Proved and sorry left

Original holes: 1. Holes closed in the item: 1, namely
`AlgebraicGeometry.ProEtale.IntegralOpenDirectImage.integral_open_direct_image`
(node `det-thm-sf-pf-adic-open`). The item itself has zero remaining sorry.
Its new private helpers `unique_mate`, `residue_killed`, `residue_discrete` and
`residue_open_image` have complete proofs.

Holes added: 2, both exact named theorem bodies `by sorry`:

- `AlgebraicGeometry.ProEtale.internal_integral_residue_criterion`, in
  `Sheaf.SixFunctors.ProEtale.IntegralResidueCriterion`, node
  `lem-sfb-internal-integral-residue-criterion`.
- `AlgebraicGeometry.ProEtale.internal_integral_direct_image_limits`, in
  `Sheaf.SixFunctors.ProEtale.IntegralDirectImageLimits`, node
  `lem-sfb-internal-integral-direct-image-limits`.

This is a decomposition, not a sorry-free proof of the target closure. The packet has
1 upper hole closed and 2 lower holes added; no claim of positive net hole reduction.
The complete Lean assembly uses the actual nonflat quotient, not an assumed flat scalar
change and not an arbitrary comparison isomorphism. No data is chosen from mere existence.

Validation: `lcompile.py --all` compiled all three modules without warnings: the direct-image
lemma in 12.6 s, the residue criterion in 5.2 s and the assigned item in 31.8 s. A text
comparison confirms that the original theorem signature and `reductionPullbackMap` body
are unchanged. All proof-step dependency unions agree with their node proof_deps lists.

## No longer needed

Removed private proof imports from the item:

- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated`
- `Sheaf.Paper.CompletedDirectImageLimits`
- `Sheaf.Paper.AdicCoefficientDatum`
- `Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`
- `Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`
- `Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients`
- `Sheaf.AlgebraicGeometry.ComparisonDirectImage`
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunction`
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
- `Sheaf.Paper.DerivedNakayamaResolution`

The explicit finite-coefficient comparison/open-finiteness argument is encapsulated by
`Sheaf.SixFunctors.FiniteOpenDirectImageCtf`; it already supplies constructibility and Tor
amplitude. Completion and coefficient-presentation tools belong to the two separate
lemmas, rather than the main assembly. Those dependencies remain needed below those
lemmas, so this packet withdraws no modules and claims no globally pruned modules.
All original public imports are retained.

Removed obsolete direct `tool_uses` entries in the item's node (the generic tools still
needed in the two lower arguments are recorded as their proof dependencies):

- `sk-lem-integral-models`
- `det-pe-derived-nakayama-resolution`
- `lem-pc-right-derived-functor-triangulated`
- `prop-weil-pbc-direct-image-limits`
- `lem-weil-pbc-standard-quotients-perfect`
- `sk-thm-pe-constructible-comparison`
- `cor-fin-deligne-open-finite-coefficients`
- `prop-weil-pbc-comparison-direct-image`
- `sk-prop-sfb-cartesian-coefficients`
- `lem-weil-pbc-ring-sheaf-change-adjunction`
- `lem-weil-restriction-of-scalars-exact`

## Where the brief, the DAG or earlier work was wrong

The existing `integral_models_stacks` uses constant scalar restriction on the
coefficient-sized small site, whereas this item uses the actual internal continuous
ring and canonical Roos augmentation. `CompletedDirectImageLimits` uses a general adic
datum and sectionwise modules. Their statements are mathematically relevant, but neither
can be applied to these internal functors by definitional equality. The missing work is
the explicit quotient-action, completion-unit and adjunction normalization retained in
the two new statements. The flat `derivedComapLowerStarIso` API cannot handle residue
scalar extension; the proof never invokes it.

The unit record `dag/units/sk-thm-sf-pf-adic.json` is still the older proper projection
formula unit, with empty realized fields; this was already noted in the item's review.
The current source for this node is the four-paragraph open-direct-image proof under
`sec-six-functors-basics`, which is followed here. No unit metadata was changed.

Edge cases checked in the arguments: empty schemes and zero objects, identity j, E=Q_l,
and torsion integral cohomology. The DVR quotient argument uses exponent one, not zero.

## New nodes

`lem-sfb-internal-integral-residue-criterion` records the integral-models criterion after
normalizing the actual internal reduction and completion. Its same-as references record
`sk-lem-integral-models` and `det-lem-integral-models-stacks`; those existing formulations
need nontrivial presentation comparisons. The equality of integral Dbc and Dctf is the
DVR Tor-resolution clause of that same source argument.

`lem-sfb-internal-integral-direct-image-limits` records the general finite-projection and
completion clauses of `prop-weil-pbc-direct-image-limits`, with the actual scalar mate
and geometric Hom bijection fixed. The same-as reference records that source theorem.
The statement retains invertibility of chi so that its inverse is meaningful, and the
specified mate rather than a bare object isomorphism. Its geometric hypotheses are
strictly more general than those of the assigned open-direct-image theorem.

The change record is `coord/changes/W8-integral-open-elaboration.md`. It records the
elaboration options that the static interface scanner classifies as a command change;
all existing public signatures and definitions remain verbatim.

The preflight requested two repairs: add a LeanSearch query alongside the recorded
type/semantic and source searches, and document the elaboration command changes. Both
are done. CartesianCoefficients and IntegralModels are retained as explicit unit-route
imports despite the fact that the main assembly uses the specialized statements.

## Second reading by W8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
