## What changed

Proved `AlgebraicGeometry.AlgebraicSpace.etale_open_chart_morphism_descent` with its
statement unchanged. The explicit subfunctor is the sheafification of the range of
the open chart map. The proof uses the existing
`AlgebraicGeometry.fppf_local_open_subfunctor_descent` for open representability;
Mathlib supplies subfunctor sheafification, gluing and uniqueness. All other glue,
atlas pullback calculations, competing-open uniqueness, scheme-test descriptions,
base change, detection and relative-base compatibility are proved here.

Added only proved private helpers in the item module and proof imports. The public
imports, public declarations and both open-chart definitions are unchanged. Updated
the existing node proof to describe the implementation. No definitions or consumer
interfaces changed, so no adaptations or change records are needed.

Validation: `lcompile.py` accepted the module in 14.6 seconds with no compiler
warnings. A direct text comparison confirms the main theorem statement is unchanged.
The delivery tool performs the final compile, axiom and preflight checks.

## Proved and sorry left

Closed: `AlgebraicGeometry.AlgebraicSpace.etale_open_chart_morphism_descent`
(node `lem-trf-etale-open-chart-morphism-descent`): 1 of 1 original holes.
Added: zero holes. Remaining in the delivered module: zero. Split off: zero.
The proof uses the existing holed theorem
`AlgebraicGeometry.fppf_local_open_subfunctor_descent`; this delivery does not
claim that dependency proved.

## No longer needed

Removed the proof imports `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite` and
`Sheaf.CategoryTheory.SiteCoveringAxioms`. The latter remains available through
the definition framework; neither is directly required for the proof.
Removed `def-trf-scheme-algebraic-space` from proof dependencies: representable
scheme sheaves and the relative-target sheaf condition follow directly from
Mathlib subcanonicity. No use of `schemeSpace` or its algebraic-space property is
needed. No other declared dependency is pruned, and no module is withdrawn.
All public imports were preserved.

## Where the brief, the DAG or earlier work was wrong

No false statement or interface defect was found. The plan is valid; Mathlib's
subfunctor sheafification implements its local-lift construction and supplies the
morphism gluing directly. Open-subspace sheafhood is not a field of OpenSubspace;
the proof establishes it for competing opens using representability and the
subcanonical sheaf condition. The route handles the empty open, full open,
identity atlas and empty test schemes without nonemptiness assumptions.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
