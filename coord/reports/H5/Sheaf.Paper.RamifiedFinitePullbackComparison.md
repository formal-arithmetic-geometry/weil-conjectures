## What changed

Replaced the proof of `WeilConjectures.RamifiedPullback.finitePullbackComparison_exists`
without changing its statement. The proof now starts from a fixed-level, objectwise module
comparison, derives naturality on module maps from the normalized generator formula, builds
natural isomorphisms of cochain complexes, and proves the adjacent tower square by testing
on the adjunction-unit generators.

The proved scalar-adjunction construction and its unit formula keep the coefficient
witnesses abstract during section calculations. Generic tensor-section helpers and the
scalar-adjunction API are in the new proved module `RamifiedFiniteTensorSections`.
The assigned module retains proved private helpers for finite pullback tensor naturality,
a generator extensionality criterion for scalar-extended finite pullback, and the
ramified completed-projection square. Extensionality removes completed scalar extension by
adjunction, retypes maps over the finite quotient using local surjectivity of the completed
projection, applies the finite pullback adjunction, then uses finite tensor extensionality.
The transition proof needs only coefficient factors equal to one. Consequently it does not
need to prove a separate quotient-representative transition equation for j.

Added `Sheaf.Paper.RamifiedFiniteModuleComparison`, which abbreviates the module functor
underlying the existing finite pullback complex functor and its existing nested generator.
Its one remaining statement asserts objectwise normalized isomorphisms at one fixed level.
It has no naturality clause, no complex or differential, and no tower square. Its source is
precisely the balanced object calculation in the original node's first two proof steps.
It is strictly part of the original argument; all subsequent coherence is proved in Lean.

Added proof imports of both new modules, `FinitePullbackTransitionGenerators`, and the
existing private proof APIs of `IntegralOperationsWellDefined` and
`IntegralReductionTowerUnrestricted`. The tensor-section module uses the existing
`CochainCoefficientArrows` API and the generic tensor proofs of the scalar-composition
implementation without importing its larger rationalization interface. Existing public imports and all shared modules are
unchanged. Updated the item's node to match this proof.

Validation: the new comparison module compiled in 43.2 seconds. The original unsplit
assigned proof typechecked in 46.2 seconds with profiling, but its next compile took
60.2 seconds. After making its scalar adjunction irreducible and adding the unit API,
the proved scalar/tensor helpers were therefore extracted to their own module to give
per-file compilation more margin. The final three-file compile passed: `RamifiedFiniteModuleComparison` in 26.7 s,
`RamifiedFiniteTensorSections` in 48.3 s, and the assigned module in 45.0 s. The original theorem signature is byte-for-byte unchanged. Node
proof-dependency lists agree with their proof-step uses, and each new node's Lean
statement matches its declaration. Temporary profiling options were removed.

## Proved and sorry left

This is a decomposition: among the declarations changed by this packet, one old hole
is closed and one strictly smaller hole is added. It is not counted as a completed
proof of the original mathematical obligation.

Closed the body of `WeilConjectures.RamifiedPullback.finitePullbackComparison_exists`
(node `lem-weil-ramified-finite-pullback-comparison`) by a complete proof from the named
module statement and existing declarations. No `sorry` remains in the assigned module.
All its private helper lemmas are proved. The additional tensor-section helper module
has zero `sorry` declarations; it is a compile-time extraction of proved code, not
another unresolved split.

One added hole remains:
`WeilConjectures.RamifiedPullback.finiteModuleComparison_exists`, in
`Sheaf.Paper.RamifiedFiniteModuleComparison`, node
`lem-weil-ramified-finite-module-comparison`. Its docstring and node give the balanced
reassociation, cancellation, inverse maps, and normalized section formula. The definitions
in that module are actual compositions and sections of the existing functors; no data is
chosen from an unproved mere existence statement in a definition.

## No longer needed

No original import was removed, and no module is withdrawn or claimed globally pruned.
The exploratory proof import of `ScalarExtensionComposition` was removed: the argument
uses only generic tensor presentation and adjunction, which are proved in
`RamifiedFiniteTensorSections` from `CochainCoefficientArrows` and module sheafification.
`def-pur-cochain-coefficient-arrows` remains needed by this proved helper node.
The original proof dependencies `lem-weil-pbc-algebraic-inverse-image-tensor-comparison`,
`def-weil-proetale-inverse-image`, `def-weil-pbc-ringed-tensor-section-calculus`, and
`def-pur-sheaf-tensor-product` are no longer direct proof dependencies of the assigned
node: their objectwise argument is isolated in the new module-comparison node. They remain
needed there and are not globally pruned.

The elementary adjacent-square proof no longer needs a separate theorem that quotient
reductions commute with j on every coefficient. Extensionality reduces both routes to
unit coefficients; every coefficient ring map preserves one. The existing completed
projection identities and finite pullback transition formula suffice. No blueprint unit
statement or prescribed unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was changed or marked disputed. The original plan correctly
identifies the objectwise balanced-tensor argument, but its final step can be shorter:
unit-generator extensionality avoids the all-coefficients calculation.

`integralOperationsProjection` is private, so the new public module-functor abbreviation
uses the explicit public projection and ring-sheaf forgetful functor instead. The existing
private adjunction and scalar-change proof lemmas remain usable through proof-only
`import all` declarations.

The blueprint ancestor helper prints `None` for this item because its creating item is
recorded as a module name. The new node follows the recorded parent identification node's
explicit ancestry to `def-weil-global-geometric-frobenius`; its `via` list retains the
intervening nodes. A full-blueprint search for the new comparison found no duplicate.

The new module statement was checked on zero modules, the empty site, equal coefficient
fields, and e=0. No flatness, boundedness, positivity, or unramifiedness is assumed. When
e=0 the supplied Coefficients hypotheses still govern existence; the tensor calculation
itself requires no positivity. The main theorem retains its original universes and all
hypotheses, including hmono and hj.

## New nodes

`lem-weil-ramified-finite-module-comparison` records the normalized objectwise comparison
for module sheaves at one fixed level, before naturality, complexes, or tower coherence.
It inherits the item's chapter and unit. Its source is Stacks 03EK and 03EL, and the
original node's first two proof steps. LeanFinder, LeanSearch, Loogle, local Mathlib reads,
and source searches found general scalar-extension and pullback-composition APIs but no
direct match for the restricted finite-quotient comparison. The node records the actual
queries and results. 
`lem-weil-ramified-finite-tensor-sections` records the proved universal-property API for
tensor sections of the specified scalar functor: extensionality, naturality, transported
adjunction and its normalized unit. It is separated for compile time, with zero holes.
It uses existing CochainCoefficientArrows and Mathlib sheafification declarations and
reuses their known generic tensor proofs.

No change record is required: no existing statement, definition, public import, or
module interface was changed.

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
