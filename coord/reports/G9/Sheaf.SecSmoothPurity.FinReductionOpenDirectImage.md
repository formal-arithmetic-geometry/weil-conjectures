## What changed

Proved `AlgebraicGeometry.Etale.finReductionOpenDirectImage` with its exact existing
signature. The proof specializes the existing coefficient-generic topological invariance
API to `ModuleCat Λ`, takes the resulting invertible reduction adjunction unit, and
whiskers it by the direct image along `j`. Two `lowerStarComp` isomorphisms and
`Scheme.Hom.liftNilradical_subschemeι` identify the composite with the required functor.
The left unitor and associator supply the functor parentheses. This is a natural
isomorphism of module-valued sheaf functors, so linearity and naturality are built into
its factors.

Added the proof-only import
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance` and retained
`WeilConjectures.AlgebraicGeometry.ReductionUniversalHomeomorphism`.
All public imports, declarations, signatures, universes, and visibility are unchanged.
Updated the item's DAG proof, proof dependencies, and proof origin to match the Lean
argument, and withdrew its obsolete specialized-composition tool approval.

The source's reduction comparison is the first paragraph of
`literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/`
`sk-prop-a1-kummer/thm-fin-open-degree-zero.proof.md`. The unit record
`dag/units/sk-prop-a1-kummer.json` has no realized statement or step at this node;
the unit route is preserved. Searches used the prescribed LeanFinder, Loogle, and grep
interfaces, plus source searches. Mathlib's adjunction equivalence instances provide the
invertible unit; the project already provides both geometric comparison APIs.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.finReductionOpenDirectImage`
(node `lem-fin-reduction-open-direct-image`).

Added 0 holes. Split off 0 statements. No `sorry` remains in the delivered Lean module.
No definition, statement, or consumer adaptation is part of this delivery.
The server single-file compile passed cleanly in 2.7 seconds using `lcompile.py`.

## No longer needed

Removed these proof-only imports and their corresponding dependencies from this item's
proof route:

- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`, node
  `lem-weil-pbc-inverse-image-composition-module-linear`: the existing generic
  `lowerStarComp` already supplies the comparison directly for `ModuleCat Λ`.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`, node
  `prop-weil-pbc-inverse-image-modules-exact`: no transport between module encodings
  or lifting of abelian maps is necessary.
- `Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance`, node
  `thm-weil-pbc-universal-homeomorphism-invariance`: the generic
  `isEquivalence_upperStar` in the underlying topological-invariance API supplies
  precisely the equivalence required, without the bundled cohomology and coherence
  conclusions.

The proof does not use the open-immersion hypothesis; its existing signature and the
statement dependency `def-weil-open-immersion` are preserved. Only its redundant
proof-dependency occurrence is removed. The reduction map factors through the target
reduction for every morphism from a reduced scheme. These are pruning claims for this
item's proof route, not claims that no other target branch needs those modules.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The original DAG unnecessarily passes through the
SheafOfModules lifting API even though the assigned statement uses ModuleCat-valued
sheaves and the project already has coefficient-generic topological invariance and
composition isomorphisms. The shorter route proves the unchanged statement.

Checked the unrestricted hypotheses: no reducedness, Noetherianity, coefficient torsion,
finiteness, nonemptiness, or constructibility is introduced. Empty schemes, the zero ring,
and already reduced schemes use the same categorical construction. The commuting square
is supplied by the reduction universal property, rather than an additional assertion
about restriction of nilradicals. All factors are isomorphisms of the exact source and
target functors in the theorem.

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
