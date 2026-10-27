## What changed

Filled thirteen of the nineteen original theorem holes in
`Sheaf.Paper.SfImmersionCompletedPullbackComparison`.
The coefficient comparisons use their quotient and finite-projection normalizations.
The ordinary derived comparison follows from universal left-derived uniqueness.
The strict completed comparison is uniquely determined by its intrinsic completion
unit and the completion reflector. The mate factorization follows from the
adjunction triangle identity. The strict Roos maps are fixed by both coordinates,
and the termwise limit comparison by its projections.

Only this Lean module is changed. All forty-four original public declaration
signatures and the public import list are unchanged. Additional helpers are private
and completely proved. No definition body is changed and no source-library file is
changed. The node records both the proved parts and the retained proof plans.

## Proved and sorry left

Closed 13 original holes; added 0 holes; split off 0 statements. The proved theorem
names below are in `AlgebraicGeometry.Scheme.ImmersionCompletedPullback`:

- `quotientEquiv_exists`
- `completedRingIso_exists`
- `moduleObj_eq`
- `moduleObj_eq_naturality`
- `derivedIso_exists`
- `moduleTowerEvaluation_eq`
- `strictIso_exists`
- `ordinaryToCompleted_eq`
- `complexEvaluation_eq`
- `roosIso_exists`
- `roosMap_exists`
- `roosInclusion_exists`
- `termwiseLimitIso_exists`

Exactly six original `sorry` bodies remain, each as the entire proof of its existing
public theorem, with its source and proof in words already in the docstring:

- `finite_compatibility`
- `completedProjection_compatibility`
- `actualCompletedProjection_compatibility`
- `roosRlim_exists`
- `rlimComparison_roos`
- `immersion_completed_pullback_comparison`

All nineteen declarations are attached to the existing node
`lem-sf-immersion-completed-pullback-comparison`. No new node or holed helper is added.
The retained six holes are unfinished work; the delivery does not claim the final
immersion theorem is proved. Focused experimental proofs are not counted as delivered
proofs. The delivery tool checks compilation, consumers, node consistency and honesty.

## No longer needed

Removed these direct proof imports from the original interface:

- `Mathlib.Topology.Algebra.Valued.LocallyCompact`
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`
- `Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage`
- `Sheaf.AlgebraicGeometry.PullbackBoundedConstructible`
- `Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`
- `Sheaf.CategoryTheory.ModulePullbackTensorIso`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Paper.ConstantCompletionEquivalence`
- `Sheaf.Paper.IntrinsicCompletionCompleted`
- `Sheaf.Paper.PbcQbarCompletedPullback`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence`

These removals are local import pruning, not withdrawal of their declarations or a
claim that the whole project no longer needs them. In particular, the final unproved
assembly still has its finite-constructibility proof plan. No module is withdrawn.

The two planned assembly nodes `lem-sf-exact-pullback-counit-normalization` and
`lem-sf-completed-pullback-mate-factorization` are not imported: their needed equations
are proved here using universal derived-functor uniqueness and a general adjunction
mate identity. The coordinate Roos clauses use
`lem-pur-roos-comparison-horizontal-coherence`, without importing
`lem-cbc-exact-product-functor-strict-limit`. The generic derived-limit work is not
claimed complete: `roosRlim_exists` and `rlimComparison_roos` remain explicit holes.
The unused top-level tool approvals for
`lem-sf-exact-functor-derived-triangulated`,
`lem-pur-roos-intrinsic-completeness-equivalence`, and
`lem-cbc-exact-product-functor-strict-limit` were removed from this node; other
consumers and the retained final argument may still require their source theory.

## Where the brief, the DAG or earlier work was wrong

The earlier draft report overstated the assembled proof count by counting focused
experimental files. This report counts only the actual delivery module: thirteen
closed original holes and six retained original holes. A general finite-compatibility
proof compiled in isolation, but its larger full-module assemblies did not give a
reliable compile below the limit, so it is not counted or delivered. The verified
strict-completion proof uses full tower and augmentation transport, followed by the
completion reflector's uniqueness; comparison of independent finite evaluations
would not establish that strict identity.
No mathematical statement is disputed or weakened, and no target is changed.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
