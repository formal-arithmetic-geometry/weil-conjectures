## What changed

Proved `AlgebraicGeometry.genus_le_of_nonconstant_smooth_proper_curve` in
`Sheaf.AlgebraicGeometry.FiniteCurveGenusMonotonicity`, preserving its full signature.
The proof privately imports FrobeniusSeparableFactorization, CurveRiemannHurwitzNumerical
and Curve.RiemannRoch. The public imports are unchanged.

Geometric integrality supplies integral sources. The pure-dimension assumptions identify
the dimensions of their unique irreducible components with one; this supplies IsCurve
and SmoothOfRelativeDimension instances. The proof handles target genus zero separately.
For positive target genus, it factors the map, identifies the intermediate genus with the
source genus in each characteristic, applies numerical Riemann--Hurwitz, and proves the
integer inequality using the positive degree and nonnegative remainder.

In positive characteristic, the field algebra is explicitly the one induced by
iterateFrobeniusOfPrime. The intermediate structure map is explicitly the second
projection, as required by the factorization. Scheme.arithmeticGenus_pullback proves the
genus equality after conversion by Scheme.genus_eq_arithmeticGenus.

A proved private helper genus_pullback_field packages these two existing APIs with explicit
structure-map instances, avoiding the broader Curve.BaseChange import.
The node proof and dependency list now record these existing interface lemmas.
The sources read were Stacks curves.tex, Riemann--Hurwitz and the proofs of
lemma-purely-inseparable-smooth-genus and proposition-unwind-morphism-smooth;
the current blueprint unit remains unchanged. The item realizes no unit step itself.

## Proved and sorry left

Closed one of one original holes:
`AlgebraicGeometry.genus_le_of_nonconstant_smooth_proper_curve`
(node lem-sfb-finite-curve-genus-monotonicity).
Zero holes added or split off; zero sorry remain in the delivered Lean module.
The proof uses the existing geometric dependency theorems, including their existing
unfinished proofs; it does not claim that those dependencies are axiom-free.

Validation: single-file compilation through lcompile.py; delivery preflight provides
its own final compilation and checks. No declarations or definitions changed signature.

## No longer needed

No original imports, nodes or modules were pruned: both geometric inputs and the
coherent base-change argument in the original plan remain needed.
An exploratory import of WeilConjectures.AlgebraicGeometry.Curve.BaseChange was removed:
the narrower arithmeticGenus_pullback API in EulerChar suffices, and the final proof
does not use genus_baseChangeField or the Jacobian invariance theorem.

The required searches were run through msearch.py (leanfinder, loogle, grep) and rg in
both library roots. No direct genus-monotonicity theorem was found.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement repair was needed. The original plan omitted the interface
between the cohomological arithmeticGenus used by this statement and Hom.genus used by
numerical Riemann--Hurwitz. The existing proved genus_eq_arithmeticGenus and
arithmeticGenus_pullback APIs resolve this without any new public lemma or definition.
The DAG now explicitly cites lem-pc-genus-agrees-sc and lem-pc-genus-base-change;
these are generic genus interface tools, not a replacement of the unit route.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
