## What changed

Replaced the hole in `SheafOfModules.ringedSite_finite_retract_dual_exact` with a
complete candidate proof. Its public statement and three public definitions are
unchanged. All auxiliary declarations are proved and private in the item module.
The independent universes `c`, `v`, and `max c v w` are preserved.

The finite-Hom isomorphism uses biproduct comparison and the proved mixed-universe
unit-evaluation calculation in `PullbackDualFreeChart`. Coordinate projections
prove naturality. Retraction gives the dual-basis and functional-expansion formulas.
The canonical mixed-universe bidual map from `RingedSiteDualityMaps` has bijective
components by the dual-basis formulas. Its inverse has the required finite-sum
formula. A generic categorical lemma proves exactness of finite powers and transports
it through the bifunctor retraction on short complexes. This uses functor laws,
monomorphism/epimorphism cancellation, and functorial homology. Restriction formulas
are explicit. No surjectivity of epimorphisms on sections is assumed.

Private proof imports: those two modules, opposite biproducts, abelian short-exact
sequences, and functor-category limits. The node records this route. No other Lean
module is changed. The command/import review is documented in
`coord/changes/C1-ringed-site-finite-retract-proof-interface.md`; it enumerates all
698 transitive importers, their current holders, and the three direct consumers'
independent import routes. No consumer adaptation is needed.

## Proved and sorry left

Original hole: `SheafOfModules.ringedSite_finite_retract_dual_exact`
(node `lem-sfb-ringed-site-finite-retract-dual-exact`).

Original holes: 1. Replacement source holes: 0. Holes added: 0. No declaration retains
`sorry`; no statements were split off and no axioms were added. The complete module has passed the delivery compiler and its initial axiom probe.

The coordinate and dual-basis block compiled in 15.4 seconds. The bidual calculation
compiled in 28.1 seconds. The complete generic-power exactness block compiled in
37.9 seconds. The unchanged public statement and the component-evaluation API also
compiled separately. The reused canonical bidual map has only `propext`,
`Classical.choice`, and `Quot.sound` among its axioms. A full delivery check returned in 52.8 seconds and exposed an overly implicit rewrite
in the evaluation formula. Evaluation now uses a proved private component lemma
whose signature matches the public types; the inverse formula uses the same interface.
The now-unused concrete commuting-square helper was removed. Exactness returns
its zero-composite witness directly, avoiding conversion to a separately fixed
short-complex witness; the redundant `hom_zero` helper was removed. The complete module
subsequently compiled and passed the initial axiom probe. Preflight requested the
change record above for the command/import changes; that record is now included.

## No longer needed

Removed the unused public import
`Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous`. The three current
importers (`RingedSiteStrictPerfectHom`, `SplitPerfectDualTorWindow`, and
`ScalarPerfectDualRealization`) obtain it through other imports.

No DAG nodes or project modules are pruned. Every original declared mathematical
dependency remains needed. Reused the existing canonical bidual construction rather
than duplicating its local evaluation and naturality proofs. Generic categorical
retraction replaces the expensive concrete short-complex construction. The private
abelian cache explicitly retains the native module-sheaf preadditive structure,
which also receives local priority, avoiding adjunction reduction during conversion.

## Where the brief, the DAG or earlier work was wrong

The existing source-library bidual/free results impose one site universe and cannot
directly instantiate this statement. The proved private mixed-universe unit chart
and canonical bidual constructions do apply.

The earlier missing published dependency has cleared. Busy compile requests are
retried. Profiling located expensive conversions through the internal-Hom
bifunctor and concrete short-complex maps. The generic finite-power retraction
avoids those repeated constructions. An earlier complete candidate reached the
60-second limit; the revised exactness block compiles substantially faster. No
limits were raised and no delivered module was split to evade the limit. Earlier
failed delivery checks pushed nothing.

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
