## What changed

Completed the comparison assembly in `Sheaf.Paper.NativeModuleConstructibilityComparison`:
coefficient transport, unchanged underlying abelian sheaves, finite limits and colimits,
restriction to strata and cover members, finite scalar/free models on exactly the same covers,
finite stratifications, native constructibility, and the ordinary derived equivalence with
every prescribed cohomological support interval. The existing public definitions and theorem
statement are unchanged. Added two component modules for ambient scalar forgetting and its
normalized restriction comparison. The restriction proof uses the direct-image naturality of
the normalized coefficient isomorphism and conjugation of adjunctions.

The scalar finite-basis argument identifies the point scalar ring with the lifted algebraic
closure by constant functions; every scalar lies in its finite simple extension. It uses the
existing internal-module/ordinary-module equivalence and a finite vector-space basis. No rank
is fixed across cover members; rank zero and the empty stratification are included.

## Proved and sorry left

Closed the original hole
`AlgebraicGeometry.ProEtale.nativeModuleConstructibilityComparison` (1 of 1).
Added and proved `AlgebraicGeometry.ProEtale.nativeScalarForgetting_isEquivalence` and
`AlgebraicGeometry.ProEtale.nativeScalarForgetting_pullbackIso` as component lemmas.
Holes added: 0. Holes left in all three delivery modules: 0. This is a proof, not an
unfinished decomposition. All three modules compiled together without warnings. A fresh final
set compile took 36.4, 47.7 and 59.7 seconds respectively under the standard limit. The
explicit axiom checks of all three named theorems show only `propext`, `Classical.choice`
and `Quot.sound`. The delivery tool performs its own independent compile and axiom checks. A profiler check of scalar recovery
passed in 33.2 seconds; an isolated main-assembly profile passed in 26.3 seconds under the
standard limit. No limit was raised and no source was split for timing.

## No longer needed

Removed the private proof imports `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`,
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`,
`Mathlib.CategoryTheory.Preadditive.Injective.Basic`, and `Sheaf.Paper.CartesianCoefficients`.
The new restriction argument does not use `sk-prop-sfb-cartesian-coefficients`; it conjugates the
strict direct-image comparison instead. Removed the obsolete top-level `tool_uses` approval
for `sk-prop-sfb-cartesian-coefficients`, preserving the order of the remaining approvals. The proof does not use sectionwise restriction of
scalars (`def-pc-sheaf-restrict-scalars`) or the sectionwise sheafification declaration
`def-weil-presheaf-modules-sheafification` directly in the main module; the scalar-recovery
component uses the monoidal sheafification adjunction. The ordinary module presentation and
local-model definitions remain. No module is withdrawn, and no adopted source declaration is
removed. Nodes can remain required elsewhere; these are removals from this proof route only.

## Where the brief, the DAG or earlier work was wrong

The previously recorded proof was mathematically adequate as a plan, but did not provide the
ambient scalar-forgetting equivalence or its inverse-image compatibility as reusable Lean
interfaces. These are the genuinely separate component arguments recorded by the new nodes.
The current item exists in the shared source; the historical quarantine row is not a request
to withdraw or delete its attachment. The native lisse predicate uses a potentially larger
cover index; the proof explicitly shrinks it using smallness of the pro-etale precoverage.

## New nodes

`lem-sf-native-scalar-forgetting-equivalence`, in
`Sheaf.Paper.NativeScalarForgetting`, records scalar recovery by restriction to algebra units,
tensor bilinearity, and monoidal sheafification. The fully faithful part reconstructs scalar
linearity of every abelian module map. The recovered action is built on the original
section groups by restricting to the algebra unit, then lifted using the existing monoidal
sheafification module adjunction; its unit supplies the comparison isomorphism.

`lem-sf-native-scalar-restriction-comparison`, in
`Sheaf.Paper.NativeScalarRestrictionComparison`, records the normalized restriction comparison
for every scheme morphism. Its proof first identifies direct images through coefficient
naturality, then uses adjunction conjugation and cancels the equivalence unit and counit.
There is no definition or statement change and no change record is needed.

## Second reading by Z7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
