## What changed

Filled both theorem bodies in
`Sheaf.AlgebraicGeometry.QcOpenIntersectionSpectralPresentation` using Mathlib.
Constructed the directed index, cofinality, compatible-tuple point, continuous
universal factorization, and equality of topologies explicitly. Proved the finite
refinement by `Finset.inf'_induction` and `Finset.inf'_union`.

Corrected the ambient order of the `IsLeast` clause with an explicit
`α := qcOpenIntersectionIndex U i₀`. All definitions and the other theorem's statement
are unchanged. The change record is
`coord/changes/qc-open-intersection-least-order.md`.
Updated the DAG proof and Lean attachment to match.

## Proved and sorry left

- `AlgebraicGeometry.Scheme.qcFiniteOpenIntersection_refinement`: original hole closed.
- `AlgebraicGeometry.Scheme.qcOpenIntersection_spectral_presentation`: corrected the
  false elaborated least-element clause to match the unchanged mathematical node,
  then proved every clause. This is a statement repair followed by a complete proof,
  not a proof of the old false elaborated proposition.

Two original hole bodies replaced; zero holes remain and zero holes were added.
Both declarations compiled cleanly through `lcompile.py` in 8.3 seconds, with no
errors or warnings. The delivery preflight checks their axioms.
No split-off lemmas or new declarations. The relevant node is
`lem-a1-qc-open-intersection-spectral-presentation` for both declarations.

## No longer needed

Removed the private proof import
`Sheaf.AlgebraicGeometry.QuasiCompactOpenIntersection`: Mathlib
`IsCompact.inter_of_isOpen` directly supplies the intersection fact.
The corresponding node `pqf-lem-qs-intersection-qc` is no longer a proof dependency
of this item. This does not assert that its other consumers can be pruned.

The planned `lem-pqf-finite-affine-cover-qc-open` and
`lem-weil-pbc-quasi-separated-affine-cover-criterion` are unnecessary here:
Mathlib's `Topology.IsOpenEmbedding.quasiSeparatedSpace` directly inherits
quasi-separatedness for open subschemes. Their Mathlib modules remain transitively
available, but those DAG steps are not used. Retained
`lem-weil-pbc-qcqs-scheme-spectral`, realized directly by Mathlib's scheme instances
and the `SpectralSpace` constructor. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The DAG's mathematical statement is correct. The original Lean least-element
clause inferred the ordinary subtype inclusion order despite the `OrderDual`
element annotation. Compiler inspection with `pp.all` showed `Subtype.instLE` in
that clause. The family containing the empty and whole opens of a nonempty scheme
is a counterexample to the original elaborated clause. Explicitly fixing the
ambient type of `IsLeast` restores the intended reverse order, without changing
hypotheses or the mathematical conclusion.

The sole DAG parent `lem-a1-sections-intersection-structure-colimit` still has the
precise assertion its plan requires; its current Lean module has no import or use
of this module, so no consumer edits are necessary. The affine-cover detour in the
DAG can be replaced by Mathlib's open-embedding inheritance API. The unit route is
preserved and no new node is introduced.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
