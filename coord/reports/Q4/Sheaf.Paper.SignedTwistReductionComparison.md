## What changed

The signed reduction comparison now constructs the normalized ordinary family from the canonical
first-line reduction and the signed-line comparison tower. Positive powers are proved by tensor
generation and induction; negative powers are proved by the scalar-dual evaluation
extensionality argument. The derived conclusions are factored through the flat-line derived
reduction interface. Two proved helper interfaces were added: first-line reduction follows from
the existing quotient adjunction and left-adjoint uniqueness; the derived comparison is obtained
from the existing ordinary-line scalar comparison and its localization factorization. No
existing declaration signature, definition, or public import is changed.

## Proved and sorry left

The packet supplies complete proof bodies for:

- `WeilConjectures.signedTwistReduction_comparison` (the one assigned original hole);
- `WeilConjectures.signedTwistFirstReduction` (new helper);
- `WeilConjectures.flatLineDerivedReduction` (new helper).

There are zero literal `sorry` bodies in the packet and no split-off holes. All three
modules compile together without errors or warnings through `lcompile.py --all`.
One original hole is closed and zero holes are added. The proof uses existing library
statements with their existing proof dependencies; it does not claim to close holes in
those imported modules.

## No longer needed

No original public import is removed and no module is withdrawn. The following original DAG
dependencies are no longer direct dependencies of the assigned theorem:

- `lem-weil-integral-twist-base-change` (`Sheaf.Paper.IntegralTwistBaseChange`): concerns
  extension between two coefficient fields, whereas this theorem needs quotient reduction.
- `lem-weil-integral-twist-derived-scalar`
  (`Sheaf.Paper.IntegralTwistDerivedScalarCanonical`): likewise concerns coefficient-field
  extension and completed constructible objects, rather than the quotient functor here.
- `lem-weil-finite-free-completed-scalar-comparison`
  (`Sheaf.Paper.FiniteFreeCompletedScalarComparison`): finite-freeness of a completed field
  extension is not needed for reduction modulo a uniformizer power.
- `lem-pur-kflat-change-of-rings` (`Sheaf.Algebra.Homology.ChangeOfRingsKFlat`) and
  `lem-weil-pbc-site-derived-tensor-descent`
  (`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`) are used
  indirectly through the existing ordinary-line derived scalar comparison. They are not
  globally pruned.

The original unit route is retained. Its `realized` record does not assign this auxiliary node
to a unit statement or proof step, and no parent dependency is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original node lists the full K-flat and base-change chain as if each prerequisite were
needed directly. The ordinary comparison only needs the canonical quotient line and the signed-
line tensor tower; the derived work follows from the already-stated ordinary-line derived scalar
comparison, transported to the exact tensor functors used by the assigned statement. The finite-
level normalization must use the old and independent-universe change-of-rings presentations
together with the left-adjoint uniqueness isomorphism.

## New nodes

`lem-weil-twist-first-quotient-normalization` and `lem-weil-flat-line-derived-reduction` are new
strict intermediate statements with complete proof bodies. Their Lean modules and DAG records
are included in this delivery. No definition or statement change record is needed because
existing signatures and definitions are preserved.

Preflight metadata repair: the new first-line node records only the theorem signature in
`lean.statement`, with its section parameters explained in the node statement. Both new
nodes now record the required LeanSearch query in addition to Loogle/LeanFinder and grep.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
