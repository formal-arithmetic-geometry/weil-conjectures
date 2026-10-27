## What changed

Filled `WeilConjectures.TensorHomCoefficientTransposes.integral_representative_laws`
in `Sheaf.Paper.CoefficientGammaRepresentatives`. The existing
`PodHomChain.counit_formula` test-object naturality clause and the inverse laws
of `Equiv` prove both compositions are identities. The first equation is checked
under the injective Hom equivalence; the second is naturality at the inverse
image of the target identity. A proved private categorical helper carries the inverse calculation, so tactics
do not inspect the large geometric chain. No existing signature, definition
body, or import changed. Explicit result-type annotations were added to
`rationalization`, `rationalGammaIso`, `rationalGamma`, `commonGamma`,
`shiftedIntegralGamma`, `rationalSourceComparison`, and
`rationalTargetComparison`, preserving their existing inferred types and bodies. The consumer check finds two downstream modules; the mathematical interfaces
remain the same and neither needs adaptation. The two rational endpoint
comparison names occur only in the defining module. See `coord/changes/V7-gamma-rational-comparison-result-types.md`.
Local irreducibility attributes keep the large Hom-chain and four restricted
adjunction constructions, plus integral/rational/common representing isomorphisms,
folded during this file's elaboration; these attributes
do not escape the module or change any definition. Both existing
`backward.isDefEq.respectTransparency` options are now true, so the elaborator
respects these boundaries rather than unfolding the constructions speculatively.
The owning node now records this naturality dependency and the two calculations.
The dependency graph has no path from that dependency back to this node.

Validation: the profiled remote compile passed in 46.0 seconds. The profile
also located repeated module-instance search and a costly final private-module
linter. `Algebra.toModule` now has priority 2000 locally, so the supplied algebra
provides its canonical module instance before unrelated normed/Lie instances.
This priority does not escape the file. Temporary profiling options and
declaration markers were removed before delivery.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.TensorHomCoefficientTransposes.integral_representative_laws`
(node `def-sf-coefficient-gamma-representatives`). Added 0 holes and split off 0
statements. No `sorry` remains in the delivered module. The proof uses the
already stated `WeilConjectures.PodHomChain.counit_formula`, whose existing
proof remains `sorry` in its own module; this delivery does not claim that
transitive dependency is proved.

## No longer needed

None. The naturality theorem is already available through the existing public
`Sheaf.Paper.PodHomChainCounitFormula` import. All existing imports support the
unchanged statement/definition interface; no import, node, module, or unit step
is withdrawn. No alternative coefficient construction or extra lemma is needed.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was necessary. The definition node had
empty proof/proof_deps despite also owning the postponed inverse-law theorem;
its proof fields now name the existing test-object naturality theorem actually
used. The unit route and all supplied full-domain and coefficient data stay as
written. The theorem follows formally from naturality for arbitrary endpoints,
including coincident endpoints, without any additional geometric hypothesis.

## Second reading by V7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
