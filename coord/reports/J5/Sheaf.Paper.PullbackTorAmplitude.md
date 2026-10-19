## What changed

Proved `WeilConjectures.sf_pullback_torAmplitude` and
`WeilConjectures.sf_pullback_finiteTorConstructible` in
`Sheaf.Paper.PullbackTorAmplitude`. All existing signatures and the body of
`sfFiniteDerivedPullback` are unchanged. Only this Lean module is delivered.
Private proved helpers handle isomorphism invariance, the two bounded-constructibility
encodings, and the canonical comparison square on ordinary and derived categories.

The proof descends the input through the existing finite-ring constructible derived
comparison, applies exact etale pullback and the source library's proved preservation
of the Tor interval, and transports back through the same canonical comparison.
The source preservation theorem uses precisely a bounded flat model and termwise
flatness preservation. This retains the unit's use of pullback preserving a flat model;
it changes the node-level presentation only. The unit record's realized lists are empty.
The theorem docstring and DAG proof, proof dependencies and origin now describe this route.

The retained proof was checked against the current shared sources on 2026-10-19.
All three existing public signatures and the complete body of `sfFiniteDerivedPullback`
match the current library exactly. The final pruned-import module compiled through
`lcompile.py` in 6.3 seconds, with no errors or warnings. The selected dependency routes were checked for a path back to this
item; none was found. No statement or definition repair, change record or consumer
adaptation is needed. Existing public imports are retained.

## Proved and sorry left

Closed the two original holes, by declaration name:

- `WeilConjectures.sf_pullback_torAmplitude`.
- `WeilConjectures.sf_pullback_finiteTorConstructible`.

Actual holes remaining in the delivered Lean module: zero. Holes added: zero.
Nothing was split off. The earlier sandbox's split modules are absent and are not
part of this delivery. The proof uses existing declared dependencies; in particular
`AlgebraicGeometry.ProEtale.comparison_torAmplitudeIn_iff` in
`Sheaf.AlgebraicGeometry.ComparisonTorInterval` still has its existing named `sorry`
(node `lem-exc-comparison-tor-interval`). No claim of axiom closure of the whole
transitive dependency graph is made.

## No longer needed

Removed these original proof-only imports and their direct node dependencies:

- `Sheaf.Paper.FiniteCoefficientFlatModel` (`lem-sf-flat-model`): the existing etale
  flat-model preservation theorem supplies the argument after comparison.
- `Sheaf.Paper.ProEtaleConstructibleOrigin` (`lem-sf-proetale-constructible-origin`):
  use the proved finite-ring derived essential-image theorem directly.
- `Sheaf.Paper.KFlatRingedToposPullback`
  (`lem-weil-pbc-ringed-pullback-preserves-kflat`): exact etale inverse image already
  has a proved Tor-interval preservation theorem.
- `Sheaf.Algebra.Homology.BoundedAboveFlatSheafKFlat`
  (`lem-pc-bounded-above-flat-kflat-site`): no direct intrinsic K-flat calculation.
- `Sheaf.AlgebraicGeometry.PullbackBoundedConstructible`
  (`lem-weil-pbc-pullback-preserves-bounded-constructible`): its source-library
  constructibility pullback lemma applies directly to the etale origin.
- `Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect`
  (`lem-weil-pbc-standard-quotients-perfect`): the finite-ring comparison needs only
  finiteness, not a complete-coefficient datum or quotient perfectness.
- `Sheaf.Paper.DerivedPullbackTensorHom`
  (`def-weil-derived-pullback-tensor-hom`): the existing canonical pullback definition
  and the unit-preserving coordinate isomorphism suffice for the finite operation.
- `Sheaf.Paper.FiniteTorAmplitudeSites`: the corollary uses the original intrinsic
  finiteTorConstructible predicate, without an additional etale predicate.
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`
  (`def-weil-derived-tensor`): no direct fixed-ring derived-tensor calculation.
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`: its required declaration
  is already exported by retained public imports; the coefficient node remains used.

Also removed redundant imports from the earlier sandbox attempt:
`WeilConjectures.CategoryTheory.DerivedCategory.Constructible` and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat`; their declarations
are publicly available through retained imports. The other retained proof imports
were tested: removing the etale module-sheaf comparison, the flat-model conversion,
or the constant-module constructibility import caused unknown-identifier errors.

The four old top-level tool approvals for
`lem-weil-pbc-ringed-pullback-preserves-kflat`,
`lem-pc-bounded-above-flat-kflat-site`, `lem-weil-pbc-standard-quotients-perfect`,
and `lem-sf-proetale-constructible-origin` are withdrawn from this node because this
proof no longer invokes them. These are local dependency prunings; another target
may still reach their modules.

## Where the brief, the DAG or earlier work was wrong

The earlier report was stale: it described two split-off holes although the retained
module already contained a complete proof using existing declarations. Replaced that
report; no split modules or new nodes are delivered. The former DAG plan needlessly
constructed a complete coefficient datum and repeated intrinsic flat-model machinery
when the proved finite-ring origin theorem and etale preservation theorem already
supply the same argument. The source statements and canonical coefficient category
are preserved, including zero objects and degenerate intervals a = b. Intrinsic Tor
amplitude itself supplies a <= b. The generic finite-ring comparison also covers the
zero ring and empty schemes, so no extra nontriviality assumptions enter the helpers.

For independent route review: the new uses of
`lem-weil-pbc-finite-ring-constructible-derived-origin`,
`lem-exc-comparison-tor-interval`, `lem-trf-open-square-exchange`,
`lem-weil-pbc-comparison-pullback`, `lem-sfb-etale-flat-geometric-fibers` and
`lem-sf-etale-flat-model` are generic comparison, coordinate identification and
flatness tools. They do not replace the unit's exceptional-pullback argument or
bypass any realized unit statement. No tool approval was added by this worker.
The already proved source-library lemmas used within their modules are named in
the DAG proof with exact source paths; none is restated as a new unproved theorem.

## Second reading by J5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
