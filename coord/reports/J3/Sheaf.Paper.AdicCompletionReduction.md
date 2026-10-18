## What changed

Proved exact scalar restriction by forgetting to abelian sheaves and reflecting finite
limits and colimits. Proved strict reduction compatibility with tower transitions using
the already stated transition naturality theorem. Proved completion-reduction naturality
by applying the specified scalar-adjunction Hom equivalence, using sectionwise naturality
of the quotient augmentation and the projection equation for the strict cone map.
All existing signatures, definitions and public imports are unchanged. The added private
helpers are fully proved parts of the same naturality argument. The scoped proof notation
is documented in `coord/changes/adic-completion-reduction-proof-context.md`.

## Proved and sorry left

Closed three of the five original holes:
- `AlgebraicGeometry.Scheme.adicRestrictScalars_exact`.
- `AlgebraicGeometry.Scheme.adicReductionComplexMap_step`.
- `AlgebraicGeometry.Scheme.adicCompletionReduction_naturality`.

Two original holes remain, both attached to
`lemma-weil-pbc-adic-completion-reduction`:
- `AlgebraicGeometry.Scheme.adicReductionAdjunction_bijective`.
- `AlgebraicGeometry.Scheme.adicCompletionReduction_isIso`.

Added zero holes and zero split-offs. The main file compiles cleanly through lcompile.py.
The naturality proof uses the original, still-stated scalar-adjunction bijectivity theorem.
An isolated diagnostic proof of the bijection compiled, but its combination with the
three delivered proofs exceeded the fixed 60-second module limit. That exploratory
route is not included. It constructs the ordinary scalar adjunction sectionwise,
derives it using resolving-class essential constancy and derived-adjunction compatibility,
and identifies the unit with the unique quotient augmentation. The next attempt needs
to reduce the cost of the concrete scalar functors and transport equalities, while keeping
the entire module within the compile limit. The remaining completion-isomorphism proof
still requires the Koszul-tower computation in steps 1-5.

## No longer needed

None. The unresolved completion-isomorphism and derived-adjunction arguments retain their
planned dependencies. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement was changed or disputed. The transition naturality needed for
`adicReductionComplexMap_step` was already proved in `CompleteCoefficientDatum`.
Coefficient-universe sheafification instances must be supplied explicitly when reflecting
exactness through abelian sheaves; unconstrained universe inference does not suffice here.

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
