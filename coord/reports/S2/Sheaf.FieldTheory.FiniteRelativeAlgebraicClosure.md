## What changed

Proved `algebraicClosure.finite_of_fg` in
`Sheaf.FieldTheory.FiniteRelativeAlgebraicClosure` without changing its signature.
Added one proved private helper,
`linearIndependent_adjoin_of_algebraicIndependent`: algebraic independence over
an extension field preserves linear independence of its constants when adjoining
the variables to the base. The proof compares coefficients of multivariate
polynomials and then localizes the polynomial subalgebra.

Choose a transcendence basis and let L be its generated field. Finite field
generation and algebraicity make K/L finite. Algebraic independence persists to
A, the relative algebraic closure. A k-basis of A remains linearly independent
over L in K by the helper, so its index type is finite. It is therefore a finite
k-basis of A. Updated the existing node's proof, proof_deps and proof_origin to
this complete route. No new public statement or module is introduced.

Validation: the final module compiled cleanly through `lcompile.py` in 3.2 s.
A source check confirmed the original theorem signature verbatim, zero holes,
and the 100-column limit. The only changed node fields are `proof`,
`proof_deps`, and `proof_origin`; the dependency list equals the union of step
uses. Delivery runs the required independent preflight and axiom checks.

## Proved and sorry left

Closed the sole original hole: `algebraicClosure.finite_of_fg`
(`lem-zl-finite-algebraic-closure`). The private helper is completely proved.
Holes closed: 1. Holes added: 0. Holes left: 0. No split-off statements.

## No longer needed

Removed proof imports `Mathlib.FieldTheory.FinTrdeg` and
`Mathlib.FieldTheory.RatFunc.Basic`, and the redundant direct import
`Mathlib.FieldTheory.IntermediateField.Adjoin.Basic` (available transitively from
`Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis`). The new proof uses
an arbitrary transcendence basis, not its finite indexing, and compares linear independence directly rather
than computing rational-function degrees.

Dependencies no longer used by this proof:

- `lem-weil-pbc-finitely-generated-field-finite-transcendence-basis`:
  replaced by the existing Mathlib leaf `lem-exc-transcendence-basis-exists`.
- `def-weil-rational-function-field`: the generated field is used directly as
  the fraction field of its polynomial subalgebra.
- `lem-zl-rational-function-degree`: coefficient comparison and localization
  directly preserve the basis, so no one-variable degree equality is needed.

These are existing Mathlib leaves; no project module is withdrawn. The entire
maximal-finite-subextension argument in the old plan is unnecessary. All original
public imports are preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The original plan was mathematically
valid but longer than necessary. Its two main comparison/maximality arguments
can be replaced by one basis argument. This works in arbitrary characteristic,
including inseparable algebraic extensions, and when the transcendence basis is
empty. The public theorem has the original two independent universe parameters.
The helper allows arbitrary index types and assumes no separability or finite
extension hypothesis. No unit statement or unit proof step is bypassed.

Searches through the launcher used LeanFinder (relative algebraic closure in a
finitely generated extension), Loogle (`AlgebraicIndependent, LinearIndependent`),
and grep (linear independence/disjointness after adjoining variables). No existing
complete theorem was found. The proof uses the inspected Mathlib APIs directly.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
