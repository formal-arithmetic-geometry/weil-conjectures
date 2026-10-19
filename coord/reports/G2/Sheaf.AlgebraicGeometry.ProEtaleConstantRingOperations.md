## What changed

Proved `AlgebraicGeometry.Scheme.proEtaleConstantRingComparison_isIso` in
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`. Compare the two left adjoints to
sections at the base-changed terminal object, then identify the specified coefficient map
with the component of their uniqueness isomorphism by computing its transpose. The
constant-section normalization is checked, not replaced by an arbitrary isomorphism.
All existing declaration signatures, definitions, public imports and instance attributes
are unchanged. No additional import or open namespace command is needed. Removed the
unused proof imports `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
and `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`; the latter's public declarations
are already available through the retained public imports.
Updated the existing node's proof, proof dependencies and proof origin with these steps,
retaining its earlier module-adjunction construction steps.

## Proved and sorry left

Closed one original hole:
`AlgebraicGeometry.Scheme.proEtaleConstantRingComparison_isIso`
(node `def-weil-pbc-proetale-operations`).
No holes remain in the item; no holes or new declarations were added elsewhere.
This is a proof, not a decomposition. The proof compiles through `lcompile.py`.
`#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

Removed the proof imports `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
and `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`. No node is removed. Both public imports
are retained for
the published finite-coefficient interface and canonical ring-module operations used by
the definitions below the theorem. The theorem's proof itself needs only the published
inverse-image definitions and finite-limit preservation, Mathlib's constant-sheaf and
sheafification adjunctions, terminal-object preservation, and uniqueness of left adjoints.
It needs no finite-coefficient comparison theorem, continuous-function calculation,
set-sheaf algebraic-structure transport lemma, or new intermediate theory. The original
node's tensor dependency remains necessary for its unchanged module-adjunction steps.
An initially tried direct import of
`Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal` was unnecessary and is absent.
`ProEtaleInverseImage` remains reachable through the unchanged public interface.
`CochainTensorUniverses` supplies monoidal and colimit instances for tensor complexes,
none of which this file's declarations use. Its direct import edge is removed; any
effect on the complete targets' import closure is left to the ledger.

## Where the brief, the DAG or earlier work was wrong

The existing node's proof described the canonical module adjunction but did not describe
the arbitrary constant-ring comparison added to its recorded Lean interface. The appended
steps now describe that proof. The original theorem docstring's set-sheaf argument is
valid, but the terminal-section adjunction argument is shorter with the available API.
It works also for the zero ring, an empty source or target, and infinite coefficient rings:
no part of the argument requires distinct constant sections or a nonempty terminal scheme.
The unit's statement and realized proof steps are untouched.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
