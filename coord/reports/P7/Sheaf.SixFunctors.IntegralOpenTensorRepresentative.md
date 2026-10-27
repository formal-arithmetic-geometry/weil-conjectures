## What changed

Filled `WeilConjectures.integralOpenTensorRepresentative` from `r.strictModel`.
The proof retains the supplied K-flatness witness, evaluates the single strict
representative equation, applies the degreewise tensor component equation, and
uses the two `CoefficientReductionPresentation` equations. Naturality of the
specified localization factors and reduction evaluations gives the required
finite-component identity; cancellation of isomorphisms finishes the argument.

Added a proved private `exactSquare_fac` helper for the component formula of an
exact derived square, using the public compositor and natural-isomorphism factor
identities in `WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate`.
That module is a proof import. The helper follows the elementary factor calculation
in the existing `DerivedExactSquareComposition` proof, without importing its full
pasted-square theorem. Local functors and representatives have explicitly typed
canonical category endpoints, avoiding elaboration across the equivalent ring and
system aliases. No shared module or public definition was changed.

Updated the item's node proof, proof dependencies, and proof-origin note to record
this factor calculation.

## Proved and sorry left

Closed the sole original hole, `WeilConjectures.integralOpenTensorRepresentative`
(node `lem-sf-integral-open-tensor-representative`). Item holes remaining: zero.
Holes added: zero. Split-off statements: zero. The private helper is proved.
Existing dependency obligations are used through their declared interfaces.

Validation: the complete single-file compile passed without warnings in 42.7 s,
within the 60 s limit. Delivery additionally runs the required probe and preflight.

## No longer needed

The planned dependency `lem-pod-derived-exact-square-composition`, module
`Sheaf.CategoryTheory.DerivedExactSquareComposition`, is unnecessary for this
proof: its component factor calculation follows directly from the exact
localization API. It was not imported, and its edge is removed from this node's
proof dependencies. No existing import was removed and no module was withdrawn.
The strict-model and coefficient-evaluation dependencies remain necessary.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The unit route is retained;
the unit record has no realized statement or proof step replaced here.

LeanFinder returned general localization and derived-factor interfaces rather
than the specialized result. Loogle found `mapDerivedCategoryFactors` and related
normalization lemmas. The launcher grep query gave no exact match; local searches
of Mathlib and both library roots found the public compositor factor formulas and
the existing private square-factor calculation. These give the direct route above.
The argument uses no boundedness, nonzero-object, or positive-index hypothesis
beyond the existing convention that index n means coefficient exponent n+1.
It therefore retains the empty-open, zero-complex, n=0, and unbounded cases.

## Second reading by P7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
