## What changed

Replaced the proof hole in
`AlgebraicGeometry.ProEtale.QuotientChange.scalar_pullback_square_coherence`.
The public definitions and statements are unchanged. The proof first establishes
ordinary scalar/pullback composition coherence by conjugating the specified
adjunctions and using faithfulness on underlying sheaves. It then uses the
given normalization and cancellation on K-flat representatives to derive
composition coherence, and pastes the two factorizations of the commutative square.

Added the private proof import
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence`
for the canonical compositor's counit formula, and
`WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift` for the existing
K-flat representative theorem. Updated the theorem's proof
explanation and its node's proof, dependencies, and proof origin.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.QuotientChange.scalar_pullback_square_coherence`.
The packet contains zero `sorry`s; no holes added and no split-off statements.
The derived composition and square-pasting arguments are fully proved; the
required delivery preflight checks the complete module and its axioms.

## No longer needed

The direct planned dependency
`lem-sfb-kflat-scalar-comparison-normalization`
(`Sheaf.Paper.KFlatScalarComparisonNormalization`) is unnecessary for this proof.
The existing generic `DerivedCategory.exists_kFlat_iso`, recorded under
`sk-def-sfb-derived-tensor-hom`, supplies the needed internal-module representative.
The supplied internal normalization and cancellation of the derived computation counits
replace the passage through section modules and its theta-composition theorem.
This does not withdraw that module or claim that its other consumers disappear.
No existing imports or modules are removed.

## Where the brief, the DAG or earlier work was wrong

The original proof plan was longer than necessary: the internal comparison can
be treated directly through its computation counit. The theorem needs only the
commutativity equation of the chosen square. No incorrect statement or definition
was found, and the blueprint unit's route is preserved.

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
