## What changed

Replaced the sole sorry in
`Sheaf.AlgebraicGeometry.ProjectiveBundleFiberDegree` by a proof from two strictly
smaller intermediate statements. The original public theorem signature and all
public imports are unchanged. All added imports are private proof imports.

The item now proves four private helpers: `standard_chart_frame`,
`exists_standard_degree`, `standard_twist_degree_le`, and `line_power_to_twist`.
Chart frames are constructed using the polynomial chart-ring equivalence, unique
factorization, and the existing affine invertible-sections theorem. The rank-two
case uses the existing projective-line classification. Higher rank reduces to a
unit-cocycle calculation, after which the item itself rescales frames and glues
the isomorphism. Tensor cancellation and induction prove the integer-power
comparison, including negative powers. Distinct twists are separated by the
vanishing of negative-degree global sections and the nonzero constant section
of the zero twist. Pullback along the inverse fibre isomorphism finishes the
original statement.

Added two modules, each containing one public intermediate theorem with a source,
a complete proof in words, and a matching new DAG node. Updated the item's proof
steps and dependencies to describe the Lean proof. No shared definition,
existing statement, source-library module, or other existing node was changed.

## Proved and sorry left

The original upper hole in
`AlgebraicGeometry.ProjectiveBundlePicardClassification.projective_bundle_fiber_degree`
is replaced by a complete Lean proof from the intermediate declarations. Its
module has zero remaining sorries. This is a decomposition, not a complete proof
of the original mathematical obligation: one upper hole closed, two lower holes
added, net minus one before accounting for the existing dependency closure.

The two added sorries are:

- `AlgebraicGeometry.ProjectiveBundlePicardClassification.exists_projective_bundle_fiber_twist_model`
  in `Sheaf.AlgebraicGeometry.ProjectiveBundleFiberTwistModel`, node
  `lem-sfb-projective-bundle-fiber-twist-model`.
- `AlgebraicGeometry.ProjectiveSpace.exists_standardUnitCocycle_normalization`
  in `Sheaf.AlgebraicGeometry.ProjectiveSpace.StandardUnitCocycleNormalization`,
  node `lem-sfb-projective-standard-unit-cocycle-normalization`.

There are no sorries inside definitions, private helpers, or the combining proof.
No arbitrary data definition is chosen from an unproved existence theorem. The
existential fibre model is eliminated only inside the theorem proof.

## No longer needed

No original public import was removed, and no module is withdrawn. The item did
not previously have private proof imports to remove.

The original direct proof dependency `lem-sfb-affine-space-invertible-trivial`
(module `Sheaf.AlgebraicGeometry.AffineSpaceInvertibleTrivial`) is unnecessary for
this proof: `standard_chart_frame` proves the needed chart triviality directly
from the existing polynomial chart-ring equivalence and affine invertible-section
API. This does not claim that the module is globally unreachable.

The finite-locally-free and projective-bundle quotient geometry dependencies are
needed by the new fibre-model node. They remain in its dependency list rather
than being claimed as pruned. Generic module-sheaf gluing remains needed through
the existing `isoOfIsFreeGenerator` API. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

No false statement or broken tool was found. The original plan names the
residue-field fibre comparison and the higher-dimensional overlap calculation
in prose, but the declared dependencies do not directly supply these two typed
conclusions. Existing projective-line classification handles only rank two.
Mathlib and repository searches did not find either missing comparison.

The new obligations separate geometry of the normalized tautological line from
the function-ring calculation. Neither states the original degree classification
under another name: the first involves only the scheme and its degree-one line,
with no arbitrary invertible module; the second involves only units and their
cocycle, with no module sheaf or gluing conclusion. The item proves the bridge
between them, all integer-power comparisons, and uniqueness.

Edge cases: rank two uses the existing projective-line theorem and never invokes
the three-coordinate cocycle statement. For rank at least three, repeated indices
force diagonal units to be one, and the distinct triples connect all overlap
exponents. The rank bound ensures that degree zero has a nonzero constant section
and that negative-degree vanishing applies. No nonemptiness or reducedness of the
base is assumed; the specified point supplies a residue field.

## New nodes

`lem-sfb-projective-bundle-fiber-twist-model` records the residue-field standard
projective-space comparison with the normalized degree-one line. Its source is
Stacks Project, Constructions, Tags 01OA, 01OE and the relative-Proj base-change
calculation, together with EGA II, Remark 4.2.7. Its conclusion stops before
integer powers or classification of any other invertible module.

`lem-sfb-projective-standard-unit-cocycle-normalization` records the double- and
triple-overlap unit calculation from Stacks Project, Divisors, Tag 0BXJ. It gives
an integer and chart units normalizing a unit cocycle. The item supplies the
module frames, their cocycle equation, and the gluing argument.

Both nodes inherit the item's chapter, unit, and blueprint ancestry. Each has
three kinds of Mathlib searches, source locations, and a stepwise proof. There
are no change records because no existing interface or other module was changed.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
