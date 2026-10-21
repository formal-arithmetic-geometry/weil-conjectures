## What changed

Proved `AlgebraicGeometry.Scheme.automorphism_completion_unit_comparison` with its
entire statement unchanged. The proof uses the existing exact transport equivalence,
the actual derived adjunction, the actual direct-image/completion comparison, and the
published Koszul reflector. It proves preservation of completeness for both adjoints,
restricts the specified adjunction with the required Hom-transpose equation, and
constructs the unique comparison for every pair of specified representatives.

Private proved helpers identify the two published completeness predicates, transport
the reflector property to arbitrary representatives, and compare reflection units.
The witness construction uses the actual coefficient restriction equivalence and the
scalar adjunction; it introduces no new data definitions or hypotheses.

Updated the node proof, proof dependencies and proof origin to this shorter argument.
Retained the unit route. No other Lean module or declaration is changed.
The public-import pruning is recorded in
`coord/changes/E2-automorphism-completion-proof-imports.md`, as required by the
first preflight. The current unchanged consumer compiles against the repaired item without warnings.

Validation: compilation through `lcompile.py`; final delivery compilation and preflight
are run by `deliver3.py`. The categorical argument includes empty generating tuples,
the zero ring and the empty scheme without separate hypotheses.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.automorphism_completion_unit_comparison`
(node `lem-sf-automorphism-completion-unit-comparison`).

Holes closed: 1. Holes added: 0. Split off: 0. No `sorry` remains in the delivery.
The proof uses existing stated dependencies, including their existing proof holes;
it does not claim to close those dependencies.

## No longer needed

Removed direct imports of `Sheaf.Paper.AdicCoefficientDatum`,
`Sheaf.Paper.IntrinsicCompletionCompleted`,
`Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`,
`Sheaf.AlgebraicGeometry.ProEtale.IsoSectionwiseInverseImage`,
`Sheaf.Paper.PbcQbarCompletedPullback`,
`Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso`,
`Sheaf.Paper.WeilCompletedKoszulLimitComparison`,
`Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`, and
`Mathlib.Algebra.Homology.BifunctorShift`.
The three public imports retained supply all public signature dependencies.
The current direct importer is `Sheaf.Paper.CompletedCoefficientPullbackLinearity`
(unclaimed). It already supplies the removed signature dependencies through its own
imports; its use of this theorem and all statements stay unchanged. Its unchanged
source compiles against this proof in an isolated validation tree without warnings. Unfinished
parents also cite the item's DAG node, so the module and node are retained.

The direct proof-dependency list no longer needs
`def-weil-pbc-adic-coefficient-datum`,
`lem-weil-proetale-isomorphism-inverse-image`,
`def-weil-proetale-inverse-image`,
`def-weil-pbc-completed-pullback`,
`lem-weil-sheaf-scalar-extension-ring-iso`,
`def-pc-tensor-complex-sheaves`, or
`lem-weil-pbc-completed-fiber-strict-limit-comparison`.
Their definitions and some supporting proofs remain transitively required by the
existing library interfaces. In particular, the strict-limit comparison remains below
the reflector and quotient comparison. These are removals of direct dependencies,
not withdrawals or claims that their modules leave the targets' import closure.
No module is withdrawn and no upstream declaration is removed.

Removed obsolete direct tool approvals for the isomorphism inverse-image lemma,
scalar-extension ring-isomorphism lemma, and strict-limit comparison. Retained the
other approvals in order. The proof additionally reuses
`lem-weil-pbc-completed-koszul-quotient-comparison` as a tool for arbitrary
representatives, and `lem-sf-constructible-canonical-completeness` for the converse
predicate bridge. Their DAG dependency closures do not reach this item; the import
check also permits the latter. No tool-approval additions were written by the worker.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original eight-step plan repeats chain-level transport
work already packaged by `pbcActualDirectCompletionIso_exists`. Its unit equation,
together with equivalence of the actual right adjoint, shows that direct image both
preserves and reflects completeness. The adjunction unit then gives preservation by
pullback. Reflection uniqueness supplies the comparison and its exact unit equation,
so this proof needs no new Koszul matrix or mapping-fiber transport construction.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
