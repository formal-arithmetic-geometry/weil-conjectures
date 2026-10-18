## What changed

Proved `CochainComplex.exists_quasiIso_degree_zero_of_bounded_degree` in
`Sheaf.Algebra.Homology.DegreeZeroComplexReplacement`, preserving its complete signature
and its three public imports. Added five proved private helpers in that module.

The shorter argument uses the uniform finite bound directly. For embeddings
`eⁿ : Kⁿ → Eⁿ` with degree-zero targets, explicitly construct the complex with terms
`Eⁿ ⊞ Eⁿ⁺¹`, differential `(a,b) ↦ (b,0)`, and monomorphic augmentation
`(eⁿ, d_Kⁿ ≫ eⁿ⁺¹)`. Its cokernel has term degree at most one less than the bound
on K. The existing proved kernel-to-shifted-cone comparison then supplies a
quasi-isomorphic complex whose terms obey this smaller bound. Natural-number
induction finishes, with the identity at bound zero.

Added the proof-only import
`WeilConjectures.Algebra.Homology.KernelShiftedMappingCone`. Import-direction checking
confirmed that it does not create a cycle. Updated the theorem proof docstring and
its existing DAG node's proof, proof dependencies, proof origin, and obsolete
`tool_uses` approval to describe the finite route. The unit record has no realized
statement or step for this node; the change stays below the fixed unit route.

Validation: the complete module compiled without warnings via `lcompile.py`.
An explicit `#print axioms` check for the public theorem reported exactly
`propext`, `Classical.choice`, and `Quot.sound`. The temporary print command was removed.

## Proved and sorry left

Closed the original one hole:
`CochainComplex.exists_quasiIso_degree_zero_of_bounded_degree`
(node `lem-sf-degree-zero-complex-replacement`).

Proved all five private helpers: `degree_zero_object`, `degree_iso`,
`exists_mono_complex_degree_zero`, `exists_quasiIso_degree_pred`, and
`exists_quasiIso_degree_zero_of_term_bound` (inside namespace `CochainComplex`).

Holes closed: 1 of 1. Holes added: 0. Split-offs: 0. Remaining holes in the
item or added elsewhere by this delivery: none. The main theorem's checked axiom
closure contains no `sorryAx`.

## No longer needed

Removed these direct proof imports:

- `Sheaf.Algebra.Homology.SubcategoryRightResolution`: the finite cone construction
  applies directly to an unbounded complex, so no bounded-below resolution or
  truncation splice is needed. Its node
  `lem-weil-pbc-subcategory-right-resolution-05T6` is removed from the proof dependencies
  and from the existing top-level `tool_uses` approval.
- `Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels`: the new proof
  constructs no elementary pushout. Neither `lem-weil-pbc-abelian-pushout-mono` nor
  `lem-weil-pbc-pushout-cokernel-iso` is needed by this proof; both are removed from
  its proof dependencies.
- `Mathlib.Algebra.Homology.HomologySequence`: the item now applies the proved
  kernel-to-shifted-cone theorem instead of deriving a quasi-isomorphism from the
  long exact sequence itself. `lem-weil-pbc-complex-ses-homology-long-exact` is no
  longer a direct proof dependency. Long exact homology sequences remain used
  transitively inside the proved kernel comparison; this is not a claim that
  homology-sequence theory leaves the whole import closure.

The original weighted-index termination, finite rounds, and eventual stabilization
construction require no new nodes or modules. The retained definitional dependencies
are `def-sp-abelian` and `def-weil-abstract-derived-category`.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The original proof plan is unnecessarily general for
the stated uniform finite bound: simultaneous embedding into a degree-zero complex,
followed by its cokernel and shifted cone, lowers the term bound everywhere at once.
The stronger private induction only needs a bound on terms of the current complex,
which is essential because the bound decreases during induction while the original
global bound on all objects does not. The zero-bound and one-bound cases are handled
by the same proof, including truncated natural-number subtraction. All complex data
are explicitly constructed; no arbitrary object is extracted from an unproved
existence theorem. No definition, public signature, or consumer required adaptation.

The dry run requests a change record for the added `open scoped ZeroObject`
command. `coord/changes/degree-zero-complex-replacement-zero-object-scope.md`
records it and the zero-consumer check. This is an elaboration scope for this file,
with no new exported instance or notation registration.

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
