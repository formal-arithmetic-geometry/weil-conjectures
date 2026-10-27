## What changed

Replaced the sorry in `Sheaf.Paper.CoefficientRestrictedTensorComparison` by an explicit
composition of derived isomorphisms. Private proved helpers identify intrinsic constant
realization with the ordinary constant sheaf and transport the ordinary monoidal structure.
A new proved generic theorem chooses flat-term K-flat representatives and computes the
published tensor after an exact flat-preserving monoidal left adjoint. The final proof
combines those computations with
constant-sheaf pullback and the counit of the target scalar equivalence.

Added `Sheaf.Algebra.Homology.ConstantRingTensorRepresentatives` and
`Sheaf.Algebra.Homology.ConstantRingDerivedTensorFlatFunctor` with the fully proved
generic representative computations, and `Sheaf.Paper.CoefficientFixedPullbackFlat`,
isolating the ordinary flatness step. Profiling identified expensive comparisons between
monoidal presentations. The proof uses the tensor API's canonical ring and module aliases,
its cached tensor structures, and no redundant source monoidal instances. The localization
isomorphism circuit is checked first with abstract categories in `localizationTensorIso`,
then specialized to the site. The source representative computation and its image under
the functor are placed in separate modules after improving these instance comparisons.
`nativeCochainTensorComparison` checks the complete native localization computation over
abstract abelian monoidal categories, including image K-flatness preservation, before
instantiating it with sheaves. Its private
proof uses the tensor API's caches for the underlying tensor data.
The final generic computation compiles in 5.0 seconds. The source representative module
compiles in 1.7 seconds, the ordinary flatness statement in 9.4 seconds, and the item in
43.4 seconds, all without warnings.
Updated the item's proof steps, dependencies and origin to describe the actual proof.
All five original public imports remain. The added imports are private proof imports.
No other existing Lean module or node is changed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.coefficient_restricted_tensor_comparison`; its module now has
zero sorry occurrences. The private helpers `fixedConstantIso`, `fixedScalarsMonoidal`,
`flatRepresentative`, `localizationTensorIso`, `nativeCochainTensorComparison` and the new public
`CategoryTheory.ConstantScalarRestriction.constantRingDerivedTensorComparison` have
complete proofs. The new public
`CategoryTheory.ConstantScalarRestriction.constantRingTensorRepresentatives` also has a
complete proof. These representative computations add no holes.

Added one hole:
`AlgebraicGeometry.Scheme.coefficientFixedPullback_preservesFlat`
(`lem-sfb-coefficient-fixed-pullback-flat`). Its proof is exactly `by sorry` in its own
module, with the source, complete argument in words and edge cases documented.

This is a decomposition: one original hole closed and one strictly simpler ordinary
flatness hole added, for net zero holes closed. No derived comparison is assumed by the
new theorem. It concerns a single ordinary flat sheaf and has no derived object, complex,
constant tensor factor or chosen inverse-equivalence object among its inputs.

## No longer needed

The proof no longer uses `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` or its module
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`. It computes directly on
flat-term K-flat representatives using the already proved resolution, rigidity and
flat-term functor declarations. Remove that dependency from this item's proof route;
other consumers of the general theorem are unaffected. No Lean module is withdrawn.

No original public import is removed. The unit's realized statement and
all its realized proof steps remain in place.

## Where the brief, the DAG or earlier work was wrong

The statement is correct on the zero ring, zero module and empty schemes, as well as
without boundedness or finiteness assumptions. The general derived monoidal comparison
API has a successor constraint on the coefficient category's Hom universe, whereas this
item has the independent universe `max v (u + 1)`. Direct representative computation
avoids that constraint. The ordinary flatness comparison with the coefficient-sized
fixed-scalar presentation is the missing substep in the original plan.

The existing `inverseImageModule_preservesFlat` theorem is on the original pro-etale
module-object presentation. It cannot be applied directly to the arbitrary independent
coefficient universe in this item. The new node records the required ordinary
specialization and its route through the existing algebraic inverse-image flatness
criterion.

## New nodes

`lem-sfb-coefficient-fixed-pullback-flat` states ordinary flatness preservation by
`coefficientProEtaleFixedModulePullback`. Its source is Stacks Tag 05VD, with Tag 03CY
for the constant-scalar presentation. Three actual search kinds are recorded. Its
argument transports the ordinary algebraic inverse-image flatness criterion through
the constant-scalar equivalences. This is a genuine part of the original flat-term
representative argument, strictly simpler than the assigned unbounded derived tensor
comparison. No change record is needed because no existing interface was changed.

`lem-sfb-constant-ring-derived-tensor-flat-functor` records the fully proved generic
representative computation. Its assumptions concern the ordinary functor; it derives
its tensor comparison from the existing resolution, rigidity and flat-term K-flat
preservation declarations. It adds zero holes and makes the universe-independent
comparison reusable by other coefficient-site proofs.

`lem-sfb-constant-ring-tensor-representatives` records the fully proved source part:
choose two flat-term K-flat representatives, retain both individual localization
isomorphisms, and compute their published derived tensor. Its proof uses exactly the
existing resolution and cochain tensor rigidity declarations. Its three actual searches
and full Lean statement are recorded in its node. This adds zero holes.

## Second reading by G8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
