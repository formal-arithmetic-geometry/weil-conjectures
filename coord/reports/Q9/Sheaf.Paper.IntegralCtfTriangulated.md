## What changed

Proved `WeilConjectures.integral_ctf_isTriangulated` in
`Sheaf.Paper.IntegralCtfTriangulated`, preserving its elaborated signature and
`integralCtfProperty`. Two proved private helpers implement the elementary
isomorphism transport and interval enlargement in steps 2 and 4 of the existing node.
The proof installs exactness of each actual `integralDerivedReduction`, applies the
finite-stage quantitative shift/extension clauses, and intersects the resulting
uniform interval property with integral bounded constructibility. The zero argument
uses finite-stage zero closure and shifts to prove vanishing in every degree, hence
the same interval [0,0] at every level. This also covers degenerate intervals and all
integer shifts; minimum/maximum bounds remain ordered and independent of the level.

Updated the existing node's zero argument and proof dependencies to match this proof.
No new modules, public declarations, definitions, instances, or mathematical interfaces.
The explicit instance lambda binder is renamed from `n` to `_n` to remove the
original unused-variable warning; this is alpha-renaming only, with identical
elaborated type. Added `CategoryTheory.Limits` and the `ZeroObject` scope for the
proof notation; recorded these changes in
`coord/changes/Q9-integral-ctf-proof-context.md`.

Validation: single-file `lcompile.py` compilation; the required dry run and delivery
also compile with the declaration/axiom probes and run the stage-3 preflight.

## Proved and sorry left

Closed 1 of the item's 1 holes:
`WeilConjectures.integral_ctf_isTriangulated`
(node `lem-weil-integral-ctf-triangulated`). Added 0 holes; split off 0 statements.
No `sorry` remains in the delivered module. The two private helpers are proved.
The proof uses the existing declared integral constructibility and reduction
exactness theorems, whose independent proof work remains with their own modules.

## No longer needed

Removed these proof-only imports:

- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.Algebra.Homology.DerivedTensor`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude`
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
- `Sheaf.Paper.SfIntegralConstructible`
- `Sheaf.Paper.SfIntegralConstructibleTriangulated`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`

The proof needs only the two original public imports, `Sheaf.Paper.FiniteCtfTriangulated`,
and `Mathlib.CategoryTheory.Triangulated.Subcategory`. The original public import
closure is unchanged. The removed modules supply no additional declaration used by
this proof. In particular the unrestricted scalar-extension, alternate coefficient
model, and `sfIntegralConstructible` interfaces are unnecessary for the actual
completed-integral reduction functor already in the statement.

Removed `def-weil-derived-tensor` from this node's direct proof dependencies: no
separate tensor construction is needed beyond the universal Tor tests and the
existing finite-stage theorem. Its definition remains a transitive prerequisite of
the Tor predicate. All other declared proof dependencies are retained, and the unit
`sk-def-sf-operations` has no realized statement or proof step bypassed here.
No module is withdrawn, and no claim is made that these imports are globally unused.

## Where the brief, the DAG or earlier work was wrong

The planned zero argument was not exposed as a public interval-specific lemma by
the finite-stage theorem. Its existing zero closure and quantitative shift clause
suffice: for a chosen bound [a,b] and degree i, shift by a-i-1 and transport back
along the zero isomorphism. Thus no new zero-tensor theorem or K-flat infrastructure
is required. The DAG now records this implementation of the same zero step.
Searches through the required LeanFinder/Loogle wrappers and local sources found
no shorter theorem of uniform integral Tor closure. The finite-stage theorem and
reduction exactness already expose every non-elementary step needed.

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
