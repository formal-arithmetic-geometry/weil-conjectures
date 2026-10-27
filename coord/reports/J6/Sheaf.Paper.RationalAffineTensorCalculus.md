## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.rationalAffineTensorCalculus` from the
recorded Tate-line, inverse-image, and rational tensor-closure interfaces. Added private
proved helpers for nonnegative tensor powers, their sectionwise and single-complex
comparisons, and the natural composition of shifted tensor pullbacks. Updated the node's proof and proof dependencies
to record this argument. Existing public theorem statements are unchanged.
The two functor definitions have
explicit result types. `rationalTatePull` uses the existing definitionally equal
`moduleObjectDerivedPullback` wrapper to keep its derived pullback folded.

The constructibility proof transports the common root-cover trivializations to internal
modules, obtains finite constant local models, and uses rational tensor closure and
triangulated shift closure. Composition uses Cartesian Tate-line pullback, strong
monoidality, derived pullback composition, and addition of shifts.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.CondensedRing.rationalAffineTensorCalculus`
(node `lem-sfb-rational-affine-tensor-calculus`), the item's one original hole.
Added: none. Split off: none. Remaining holes in the delivered module: none.
The imported recorded theorems retain their existing proof obligations.
The complete proof compiled without warnings in 50.5 seconds in the development module.
The repair recompiles the retained proof against the current published build, and the
final delivery runs the server preflight against its freshly fetched `sheaf-dag` base.

## No longer needed

No original dependency is pruned. The proof uses the existing private unit comparison
from `Sheaf.CategoryTheory.InternalSectionTensorComparison` and the proved balanced-tensor
comparison from `Sheaf.CategoryTheory.InternalSectionModuleFlat`; both imports are retained.
All original public imports are retained. The newly explored direct localization proof
is not used; the existing proved helpers suffice. The localization imports are retained
to supply their monoidal instances. No existing node or module is withdrawn.
The proof does not require a new inverse-twist theorem, a new constructibility definition,
or separate higher-power local-triviality statements;
nonnegative powers are handled by finite induction using rational tensor closure.

## Where the brief, the DAG or earlier work was wrong

The original plan did not supply the explicit comparison between sectionwise slice
trivializations and internal scheme inverse image. The proposed new localization helper
is unnecessary: `IntegralRestriction.locallyFree_of_trivial_cover` already provides
raw internal local freeness, and `lisse_of_raw_free` converts it to the normalized
coefficient convention. No mathematical statement or definition was repaired. Keeping
`DerivedCategory.singleFunctors` folded before the degree-zero unit comparison avoids
elaborating its large construction. The local proof attributes keep the fixed comparisons
folded. The presentation change is recorded in
`coord/changes/J6-rational-affine-functor-elaboration.md`.
The final theorem signature was compared verbatim with the original, all Lean lines are
at most 100 characters, and the node proof dependencies equal the union of step uses.

The delivery at `c248ab4a185` passed independent review C-c248a, but landing failed
because `--apply-fixes` named only `Sheaf.Paper.RationalAffineTensorCalculus.md`.
The report's repository-relative delivery path is
`coord/reports/J6/Sheaf.Paper.RationalAffineTensorCalculus.md`; reviewer fixes to
this report must use that complete path. The launcher maps this sandbox's `report.md`
to that path. This repaired report records the path explicitly; no duplicate report
or renamed Lean module is introduced. The retained proof and node changes are reapplied
by the delivery launcher on its freshly fetched `sheaf-dag`, rather than repushing
the returned commit. There was no compiler failure or requested mathematical change.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
