## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_tateTwistDerived_of_invertible`
in `Sheaf.Targets.PoincareTateBoundedConstructible`, with its signature unchanged.
The actual first Tate twist has a proved local basis after raw inverse image. Tensor
powers inherit that basis. For negative powers, the sheaf internal-Hom comparison and
the equalizer imposing linearity give a basis for the actual categorical internal Hom.
A one-stratum finite presentation gives constructibility, and the existing proved
shifted-single theorem finishes the derived assertion. All added helpers are proved
and private. The route node now records these steps and dependencies.

The source read was the current blueprint
`literature/blueprint/latest/blueprint/sec-proetale-coefficients/sk-def-sp-tate-twist/_section.md`,
including the invertibility, integral limit, scalar extension, rank-one, tensor-power
and dual clauses. The first-twist and shifted-single declarations were read with their
nodes. Mathlib searches through msearch: LeanFinder for shifted condensed Tate
constructibility found general condensed and t-structure declarations, Loogle
`"tateTwist"` found no hits, and grep `tateTwist|boundedConstructible_shift_single`
found no hits. Local searches found the existing exact first-twist and shifted-single
helpers, so no new mathematical statements were needed.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.boundedConstructible_tateTwistDerived_of_invertible`
(node `lem-route-bounded-constructible-tate-twist-derived-of-invertible`).
Holes closed: 1. Holes added: 0. Holes remaining in the item: 0. Split off: 0.

## No longer needed

Removed these old proof imports from the item:

- `Sheaf.Paper.CompletedCondensedCoefficients`
- `Sheaf.Paper.CondensedZlReduction`
- `Sheaf.Paper.PurTwistSheafLocallyFree`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`
- `Sheaf.Paper.CondensedConstantConstructibility`
- `WeilConjectures.CategoryTheory.ModuleObjects.Free`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs`

The first five belong to the older docstring plan. Their coefficient-reduction,
completed-line, sectionwise Hom and constant-model results are unnecessary as direct
inputs here: the existing actual first-twist local basis already supplies what is
needed. The free-module API and finite inverse-image definitions arrive through the
imports that the proof uses. Existing public imports are retained as the public API.

The former direct planned dependencies `sk-prop-sfb-qlbar-colimit-x`,
`lem-pur-condensed-zl-reduction-mod-ell-power`, `lem-pur-twist-sheaf-locally-free`,
`def-pur-sheaf-hom` and `det-def-sfb-constructible-local-model` are not used as direct
steps. This does not assert those modules are globally unreachable: other library
consumers and the first-twist theorem have their own dependencies. No module or DAG
node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

At session start the item's newly generated route node had empty proof/proof_deps,
although the older `nt-target-poincare-tate-bc` node already recorded a useful five-step
proof using existing local-basis and shifted-single theorems. A concurrent stage-1
worker subsequently replaced the provisional statement and supplied a one-step
reduction through that older target. This packet preserves that worker's updated
statement and all metadata; it replaces only the proof fields with the actual Lean
argument, which avoids depending on a theorem under the old target's stale attachment. The Lean docstring retained the
older six-step coefficient-comparison plan. This delivery implements the existing
five-step route and records it on the node actually attached to the item. It does not
change either target statements or definitions. The unit route is retained: integral
roots, scalar extension, rank-one local model, tensor powers and duals, then the
shifted single complex. The arbitrary scheme domain, negative twists, zero twist and
empty scheme all remain covered.

Validation: the full item compiled through `lcompile.py` in 19.1 seconds, exit code 0,
with no warnings. The original theorem signature is textually identical, all lines
are at most 100 characters, and both newly imported Sheaf modules passed the
import-direction check. No new node or public declaration was added.

## Second reading by Y2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
