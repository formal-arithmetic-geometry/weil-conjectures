## What changed

Proved `AlgebraicGeometry.Scheme.proEtaleStructurePresheaf_isSheaf` in
`Sheaf.AlgebraicGeometry.ProEtaleStructureSheaf`. Added the proof-only import
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc`, whose proved `Scheme.isSheaf_Γ`
applies to the subcanonical big pro-etale topology. Continuous restriction along
`ProEt.forget S ⋙ Over.forget S` gives the required small-site ring-valued sheaf.
All three existing signatures and both definitions are unchanged.

Updated the existing node's proof, proof dependencies and proof origin to describe this
route. Its unit `sk-def-sf-admissible` has no realized steps affected by this change.
The single-file server compile succeeded in 2.4 seconds without warnings.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.proEtaleStructurePresheaf_isSheaf`
(node `def-pur-proetale-structure-sheaf`). Added 0 holes; split off 0 theorems.
No sorry remains in the delivered module. The source-library theorem `Scheme.isSheaf_Γ`
is proved from representability via the Gamma-Spec adjunction and subcanonicity;
it contains no sorry. This is a proof, not a decomposition.

## No longer needed

No original import was removed. No new dependency module with sorry is needed.
Removed `lem-weil-pbc-weakly-etale-composition-base-change` from the node's explicit
proof dependencies and top-level tool-use approvals: the proof uses the existing
continuous restriction theorem rather than constructing overlaps by hand.
Its Mathlib module remains transitively imported by the site definition itself.
The affine-line polynomial-evaluation argument, explicit elementwise ring gluing,
and the explicit covering-sieve gluing argument are unnecessary: representability
of every ring-Hom presheaf gives exactly the category-valued sheaf condition.
The affine-target and fpqc representable-descent nodes remain mathematical dependencies,
implemented through the proved source-library theorem; their separate statement
modules need not be imported. No existing Lean module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The earlier searches missed the proved source-library theorem `Scheme.isSheaf_Γ`
in `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc` and
`ΓSpec.representableBy` in `WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction`.
The original statement and construction are correct. Representability here is on
all schemes, followed by continuous restriction; the argument does not assume
that an affine representing scheme is an object of the small pro-etale site.
There are no interface repairs, forced consumer adaptations, or new nodes.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
