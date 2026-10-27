## What changed

Filled `AlgebraicGeometry.Etale.scalarPullback_compactification` in
`Sheaf.Paper.EtaleScalarPullbackCompactification`, preserving its signature and docstring.
Added private proof imports `Sheaf.Paper.ScalarPullbackComposition` and
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange`.
The latter supplies the proved definitional identification
`leftDerivedUpperStarCompactificationIso_eq`.
A proved private categorical helper transports the existing exact composition square
through six natural isomorphisms. The proof specializes it to the canonical
exact/left-derived pullback comparisons, identifies the transported compositors by
their definitions, takes inverses, and uses the compactification equation.
This follows both steps of the existing node without changing the unit route.
Updated its proof text to describe the general compositor indexed by `f` and
`c.comm`, avoiding substitution through dependent compactification data.

Validation: the complete proof compiled with `lcompile.py` in 8.5 seconds.
Temporary diagnostic modules, trace tactics, and profiling options were removed
before delivery; the delivery tool checks the final files again.

The source read was Stacks `sites-cohomology.tex`,
`lemma-derived-pullback-composition` (0D6D), and `sites-modules.tex`,
`lemma-push-pull-composition-modules` (03D8). The search tools found ordinary
pullback and scalar-extension compositors and generic isomorphism transport lemmas;
the existing project `scalarPullback_composition` is the applicable exact-derived
composition equation.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.scalarPullback_compactification`
(node `lem-pur-etale-scalar-pullback-compactification`).
No holes added, no split-off statements, and no `sorry` remains in this delivery.
The private transport helper is proved in full.

## No longer needed

None. Both original public imports are needed by the unchanged statement, and the
proof uses the two declared dependencies of the existing node. No nodes or modules
are withdrawn. In particular this closes the previously split obligation rather
than splitting it again.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The existing proof plan is realized directly.
Directly destructuring the compactification and substituting its equation exceeded
the compilation limit. Using the existing general-compositor identification avoids
that dependent substitution and compiles quickly; no shared definition was changed.
Properness and openness are not used by the categorical calculation; they remain
part of the compactification data. No boundedness, flatness, or finiteness hypothesis
was introduced. All steps use naturality and invertible comparisons, so the same
proof includes empty schemes, zero objects, and zero coefficient rings.

## Second reading by S2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
