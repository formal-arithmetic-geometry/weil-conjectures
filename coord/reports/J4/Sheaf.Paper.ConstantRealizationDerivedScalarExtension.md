## What changed

Proved `moduleComparison_tensor`, including the ordinary scalar-extension isomorphism and its
constant-section tensor formula. The proof constructs the inverse by transposing maps through
the ordinary module adjunction, lifts the resulting presheaf map through sheafification,
and checks the two inverse composites on pure tensors and sums. The existing naturality and
restriction constructions in the sandbox are retained. The module compiles with the current
proof-only imports. The proof-only import change is recorded in
`coord/changes/Sheaf.Paper.ConstantRealizationDerivedScalarExtension.md`.

## Proved and sorry left

Closed one original sorry:

- `CategoryTheory.ConstantScalarRealization.moduleComparison_tensor`

Two original named sorries remain:

- `CategoryTheory.ConstantScalarRealization.constantRealizationDerivedScalarExtension`
- `CategoryTheory.ConstantScalarRealization.constantRealizationDerivedScalarExtension_transitivity`

No new sorry declarations were added.

## No longer needed

None. The proof uses the existing ordinary adjunction, restriction comparison, constant-section
lemmas, and sheafification API; no declared dependency or blueprint unit step was bypassed.

## Where the brief, the DAG or earlier work was wrong

The remaining derived comparison and tower statements require the independently sized derived
adjunction and representative normalization package; the ordinary tensor comparison can be
proved directly from the already constructed mate and does not require those higher statements.
No target statement or definition was changed.

## Second reading by J4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
