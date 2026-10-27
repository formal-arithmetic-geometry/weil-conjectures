## What changed

Filled `AlgebraicGeometry.ProEtale.coefficientComparison_boundedClassical` by an
explicit derived-adjunction argument. Two proved private helpers transfer full
faithfulness from D+ to unbounded Hom sets and apply bounded truncation devissage
to the derived counit. Localization uniqueness handles the arbitrary functor D
in the unchanged statement. Both coefficient universes remain arbitrary.

Added `CoefficientComparisonInjectiveAcyclic` and `CoefficientClassicalModuleOrigin`
as ordinary-sheaf inputs. The acyclicity node uses the library’s `rightAcyclic`
predicate, asserting vanishing of all positive ordinary right-derived images. These are strictly
lower steps: the first concerns
injectives and positive ordinary derived direct images; the second only concerns
individual modules. Neither states bounded derived comparison or repackages it.

Narrowed the public import in `ConstructibleComparisonModuleExact` from the final
comparison theorem to its existing comparison-data module, permitting reuse of
its proved exactness without an import cycle. Its declarations and proof bodies
are identical. The narrowed module compiled in 20.9 s; its unchanged direct
consumers `FiniteComparisonModelRealization` and
`ConstructibleComparisonTensorTestReflection` compiled in 18.4 s and 26.9 s.
The two private derived-category helpers also compiled independently.
Removed the two redundant direct imports of shift-adjunction and
triangulated-adjunction APIs after their import-minimal helper check compiled. Updated the item’s
proof route and the stale exactness-node data
dependency. Change record: `coord/changes/D7-coefficient-comparison-exact-import.md`.

## Proved and sorry left

Closed the single original hole in
`AlgebraicGeometry.ProEtale.coefficientComparison_boundedClassical`.
The item contains zero `sorry`s. All four delivery modules compiled together:
ordinary module origin 11.8 s, injective acyclicity 8.7 s, exactness 6.6 s, and
the item 16.6 s, with no errors or warnings. Added two holes:

- `AlgebraicGeometry.ProEtale.coefficientComparison_injectiveAcyclic`
  (`lem-pe-coefficient-comparison-injective-acyclic`).
- `AlgebraicGeometry.ProEtale.coefficientClassicalModule_origin`
  (`lem-pe-coefficient-classical-module-origin`).

This is a decomposition, not a net proof: one hole closed, two added. The generic
fully faithful, single-complex counit, bounded devissage, and localization-transport
steps are complete Lean proofs. The exactness module has zero holes before and after.

## No longer needed

The item’s original proof imports only its two public statement dependencies;
neither was removed. Two redundant proof imports used during development,
`Mathlib.CategoryTheory.Shift.Adjunction` and
`Mathlib.CategoryTheory.Triangulated.Adjunction`, were removed after a compiled
helper check. Their APIs are supplied by the derived-adjunction imports.
Its new proof does not import
`Sheaf.AlgebraicGeometry.ClassicalDerivedEquivalence`,
`Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesModules`, or
`Sheaf.AlgebraicGeometry.BoundedBelowProEtaleComparison`.
The old direct proof dependencies `det-pe-classical-derived-equivalence`,
`det-pe-classical-sheaves-modules`, and `sk-prop-sf-comparison` are replaced by the
coefficient-sized underived inputs, existing exactness, and generic derived-unit
tool. The module-sheaf comparison still occurs below the new underived inputs;
it is not claimed globally unnecessary. No module is withdrawn or globally pruned.

The exactness module no longer imports
`Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison`; it imports the data
module owning the canonical constructions instead. No adopted source declaration
is removed and no proved source body is replaced by `sorry`.

## Where the brief, the DAG or earlier work was wrong

The original fixed-coefficient declarations use coefficients in `Type (u+1)`;
this item uses `Type (max v (u+1))`. They therefore do not directly instantiate
for its full universe range. The new inputs isolate the ordinary module transport
and acyclicity required at that range, rather than duplicating the entire bounded
derived conclusion. The classical-derived unit route and bounded truncation are
preserved.

The exactness module’s import and node still pointed to the final constructible
comparison after the canonical definitions had moved to the comparison-data
module. That prevented importing its proved exactness into this item. The import
repair compiles and leaves its declaration signatures and definitions unchanged.

## New nodes

`lem-pe-coefficient-comparison-injective-acyclic` records invertibility of the
ordinary unit on injectives and direct-image acyclicity of their pullbacks.
Its source is the current blueprint injective-acyclicity proof (Stacks 099U/099V),
with the constant-scalar and small-site transport written in its proof steps.

`lem-pe-coefficient-classical-module-origin` records the ordinary essential-image
step from the current blueprint module-sheaf proof, final paragraph, and the
classical set-counit criterion. It imposes no constructibility or boundedness.
The docstring covers zero rings, zero modules and the empty scheme. Both nodes
record LeanSearch, LeanFinder and Mathlib-source searches with their results.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
