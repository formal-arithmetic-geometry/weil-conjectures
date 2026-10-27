## What changed

In `Sheaf.AlgebraicGeometry.JetDiagramHilbertControl`, proved
`DiagonalJets.initial_diagram_vertices` using the shifted monomial coefficient formula,
Dickson's lemma for finitely supported natural exponents, and degree-lex enumeration of the
finite set of coordinatewise minimal elements. The proof includes upward closure and equality
with the generated orthants.

Proved `DiagonalJets.unique_supported_division` from the already stated
`MonomialDiagram.exists_unique_supported_formal_division`. The actual glue proves that any
ordered minimal-vertex family generates the initial diagram, converts the two support
predicates, and transfers uniqueness to the quotient/remainder pair.

Proved `DiagonalJets.formal_quotient_dimension` by constructing a linear equivalence from
coefficient functions on the finite set of complementary monomials of degree at most n to the
truncated quotient. Injectivity uses the least nonzero exponent and the coefficient criterion
for powers of the variable ideal. Surjectivity uses supported division followed by truncating
the remainder. Module finiteness and the dimension formula follow from this equivalence.
The coefficient criterion is the proved upstream theorem
`power_series_mem_combined_ideal_pow_iff`, specialized to the zero coefficient ideal.

All helpers are private proved theorems. Existing declaration signatures, public imports and
all definitions are unchanged. Updated steps 6--8, proof dependencies and proof origin of
`lem-trf-jet-diagram-hilbert-control` to match these proofs. No other existing module or node
was changed. Empty vertex families, empty complementary sets and zero variables are included
by the general proofs, without nonemptiness assumptions.

## Proved and sorry left

Closed 3 of the original 11 holes, with no added holes:

- `DiagonalJets.initial_diagram_vertices`.
- `DiagonalJets.unique_supported_division`.
- `DiagonalJets.formal_quotient_dimension`.

The latter two use the existing named theorem
`MonomialDiagram.exists_unique_supported_formal_division`, whose own proof remains sorry in
its existing module (node `lem-trf-supported-formal-division`); it is not copied or altered.

Eight original holes remain, all attached to the original node
`lem-trf-jet-diagram-hilbert-control` and retaining their complete source proof plans:

- `DiagonalJets.finite_and_fibre_dimension`.
- `DiagonalJets.existsUnique_taylor`.
- `DiagonalJets.taylor_dimension`.
- `DiagonalJets.taylor_diagrams_locally_finite`.
- `DiagonalJets.no_infinite_hilbert_descent`.
- `DiagonalJets.etale_principal_parts`.
- `DiagonalJets.etale_taylor_compatibility`.
- `DiagonalJets.free_variables`.

The complete changed module compiled without errors or warnings in 7.2 seconds through
`lcompile.py`, before removing the unused proof imports listed below. Delivery runs the final
compile and axiom/preflight checks against the pruned imports.

## No longer needed

Removed these nine unused private proof imports (all public imports stay unchanged):

- `Mathlib.AlgebraicGeometry.Noetherian`.
- `Mathlib.Order.WellQuasiOrder`.
- `WeilConjectures.AlgebraicGeometry.FlatUnramifiedFormallyEtale`.
- `WeilConjectures.FieldTheory.SeparableExtensionFractionFieldOfSmoothAlgebra`.
- `WeilConjectures.FieldTheory.SeparablyGeneratedDifferentialsDimension`.
- `Mathlib.RingTheory.Kaehler.TensorProduct`.
- `Mathlib.RingTheory.Etale.Kaehler`.
- `Mathlib.RingTheory.Smooth.Basic`.
- `Mathlib.FieldTheory.SeparablyGenerated`.


The new proofs reuse the existing supported formal division theorem rather than implementing
a second triangular division recursion. No new node, intermediate sorry or duplicate division
theorem is needed. No DAG node or library module is withdrawn: the untouched clauses still
need their original source proof plans, including their geometric and field-theoretic inputs.

## Where the brief, the DAG or earlier work was wrong

The planned coefficient recursion in step 7 already has an exact library declaration in
`Sheaf.RingTheory.SupportedFormalDivision`, so reimplementing it here is unnecessary. The
finite quotient proof also has an existing proved variable-ideal coefficient criterion in
`WeilConjectures.RingTheory.PowerSeriesCombinedIdealCoefficients`. No mathematical statement
was found false and no target, definition, unit statement or unit route was changed.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
