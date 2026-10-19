## What changed

Proved all eight original holes in `Sheaf.Paper.FourCorners`. Every existing signature,
definition and public import is preserved. Three proved private helpers identify the
strict constant towers and establish finite and completed coefficient composition.
No new public declarations or split-off obligations were introduced.

The completed-ring map is identified projectionwise with the conjugate of the published
profinite comparison by limit isomorphisms. Finite composition uses the published
constant-comparison composition clause and naturality of inverse-image composition.
Completed composition follows by projecting to every finite level. Dependent congruence
then transports both composition equations across the cartesian square equation.

The reduction/pullback mate is proved invertible by a shorter adjunction argument.
The published ring-sheaf adjunction compatibility identifies the other mate with its
invertible direct-image comparison. Mathlib's iterated-mates identity identifies the
double mate with conjugation between composite adjunctions, which reflects invertibility.
The node copy records this proof route and its existing dependencies.

## Proved and sorry left

Closed 8 of the original 8 holes, all under node `def-weil-pbc-four-corners`:

- `AlgebraicGeometry.Scheme.proEtaleRingExtension_obj`.
- `AlgebraicGeometry.Scheme.proEtaleReductionPullbackInv_isIso`.
- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.ringTower_finite`.
- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.integralRingComponent_naturality`.
- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.integralRingMap_isIso`.
- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.projection_comm`.
- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.integral_coherent`.
- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.finite_coherent`.

Holes left: 0. Holes added: 0. Split-offs: 0.
The complete file compiles cleanly through `lcompile.py` in 8.7 seconds;
delivery preflight checks declaration axioms.

## No longer needed

No imports, modules or DAG nodes are pruned relative to the current library.
The earlier sandbox attempt's proof-only `Mathlib.CategoryTheory.Whiskering` import
was removed; the existing imports supply that API. The direct K-flat representative calculation described
in the original mate docstring is unnecessary: the published adjunction compatibility
and iterated mates suffice. In particular, this proof does not directly invoke
`lem-pc-kflat-resolution` or `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`.
Their original statement dependencies and exported interfaces remain; the derived
constructions used here still obtain their normalizations from the existing library.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The retained attempt left two tractable holes:
integral coefficient coherence follows from finite projections, and the scalar mate's
invertibility follows formally from the published ring-sheaf change adjunction theorem.
Neither requires a new intermediate theorem. The quotient tower and constant-sheaf tower
use different sequence presentations; the proved identity-on-components isomorphism
accounts for that difference. Projection and mate calculations use `erw` at presentation
boundaries and declaration-local transparency settings.

The earlier delivery encountered a temporary-worktree checkout timeout. This session
retained that work and reran the required tool without changing its implementation.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
