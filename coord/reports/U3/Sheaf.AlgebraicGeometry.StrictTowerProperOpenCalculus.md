## What changed

Proved alpha_cartesian, alpha_vertical, alpha_horizontal and alpha_baseChange
without changing their signatures. A common reverse comparison factors through
the clopen lift. Its counit followed by pi is identity, and precomposition by it
detects maps into the upper open extension. The reverse pasting equations then
prove all four alpha clauses by cancellation.

StrictTowerProperOpenArrows gains proved generic component and cancellation APIs
and a real equality-transport wrapper. Its original alpha and every other
existing data definition, signature, attribute and public import stay verbatim.

Constructed SingleProperOpenArrows with zero holes. It independently defines the
ordinary module clopen projector, its exact-localized alpha and proper mate.
StrictTowerGammaEvaluation proves evaluation of the mate from evaluation of
alpha using the existing coefficient/exchange theorem. gamma_evaluation now has
a complete Lean proof from that result and SingleProperOpenFiniteNormalization:
it transports the single-level mate along originIso and cancels the specified
evaluation isomorphisms. The two normalization results are genuine separate
source results, detailed below; this last clause is a decomposition.

All six packet Lean modules compile through lcompile.py --all. Existing consumers
need no forced adaptations. Change records are listed under New nodes.

## Proved and sorry left

Original holes closed: five. Four are complete proofs with no new holes:

- AlgebraicGeometry.ProEtale.StrictTower.alpha_cartesian
- AlgebraicGeometry.ProEtale.StrictTower.alpha_vertical
- AlgebraicGeometry.ProEtale.StrictTower.alpha_horizontal
- AlgebraicGeometry.ProEtale.StrictTower.alpha_baseChange

AlgebraicGeometry.ProEtale.StrictTower.gamma_evaluation is decomposed into two
strictly separate normalization results. Its combining proof is complete.
There are zero sorrys in the item module, StrictTowerProperOpenArrows,
SingleProperOpenArrows and StrictTowerGammaEvaluation. All new data are actual
constructions, and all other new helper theorem proofs are complete.

New holes added: two, each exactly a named public theorem with its complete
natural-language proof and source in its docstring:

- AlgebraicGeometry.ProEtale.StrictTower.alpha_single_evaluation, in
  Sheaf.AlgebraicGeometry.StrictTowerAlphaEvaluation;
  node lem-cbc-strict-tower-alpha-single-evaluation.
- AlgebraicGeometry.ProEtale.StrictTower.singleGamma_finite_normalization, in
  Sheaf.AlgebraicGeometry.SingleProperOpenFiniteNormalization;
  node lem-cbc-single-proper-open-finite-normalization.

This is four proofs and one decomposition, not five independent closed proofs.
The packet closes five old holes and adds two lower ones, for a net of three
before the maintainer's pinned target-closure ledger calculation.

## No longer needed

No existing module, declaration or public import is withdrawn. No target-closure
module is claimed pruned. The vertical, horizontal and cube alpha clauses do not
need separate sheafwise nested-projection or base-changed-component calculations:
the proved reverse-comparison uniqueness argument replaces those planned glue
steps. The unit's statement and coherence route are retained.

The following original direct proof dependencies of the calculus node are now
used through the operation and the two normalization nodes, rather than being
reproved in the item. They remain needed transitively and are not withdrawals:

- lem-weil-tower-evaluation-kinjective
- lem-weil-pbc-ring-sheaf-change-adjunction
- def-pc-sheaf-restrict-scalars
- lem-cbc-proper-support-sheaf-composition
- lem-weil-pbc-extension-by-zero-adjunction
- prop-weil-pbc-inverse-image-modules-exact
- def-weil-finite-type-morphism
- def-weil-closed-immersion
- def-weil-quasi-separated-morphism
- lem-weil-pbc-comparison-direct-image-canonical-mate
- lem-weil-pbc-extension-by-zero-exact
- lem-cbc-proetale-extension-zero-comparison
- lem-weil-pbc-comparison-pullback
- prop-weil-pbc-comparison-direct-image
- lem-weil-pbc-coefficient-exchange-mates

The unused experimental component-extensionality API was not included in the
packet; the final proof needs only the component constructor and split cancellation.
No existing library declaration was removed.

## Where the brief, the DAG or earlier work was wrong

A cartesian square's canonical lift is an isomorphism to the chosen pullback,
not literally an identity of the chosen object. The proof uses the reverse
comparison and its invertibility, so makes no such literal-identification claim.

The alpha cube follows already from commutativity of the two vertical faces;
its two open faces supply the beta isomorphisms. The original stronger hypotheses
sp and sr and all other public binder names remain unchanged.

Kernel normalization of concrete component rewrite motives could exceed the
server limit even after elaboration succeeded. Passing the factorization to a
proved generic categorical lemma, and comparing squareG at functor level before
taking components, resolves this cost. No limit was increased and no proof file
was split merely to evade the compile limit.

## New nodes

def-cbc-single-proper-open-arrows constructs the actual single-level module
projector, exact-localized alpha and proper mate, together with proved arbitrary-B
open and clopen comparison APIs. All its data and proof fields are complete.

lem-cbc-strict-tower-alpha-single-evaluation is the exact termwise evaluation
lemma for alpha alone. It contains no proper derived direct image, finite origin
or chosen origin isomorphism; it is one remaining source result.

lem-cbc-strict-tower-gamma-single-evaluation is proved from the preceding lemma
by coefficient/exchange mate pasting and four specified counit equations.

lem-cbc-single-proper-open-finite-normalization is the single-level finite etale
scalar/site normalization. It contains no tower or evaluation index and uses
exactly the finite coherence theorem's normalized witness. It is the other
remaining source result. The report and node docstrings check identity squares,
cartesian alpha, and empty-open cases; no extra hypotheses were added to the item.

Change records:

- coord/changes/U3-strict-tower-cartesian-proof-settings.md
- coord/changes/U3-strict-tower-alpha-component-api.md
- coord/changes/U3-single-proper-open-normalization.md

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
