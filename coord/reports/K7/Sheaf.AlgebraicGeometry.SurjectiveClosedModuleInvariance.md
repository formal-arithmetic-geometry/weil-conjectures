## What changed

Proved `AlgebraicGeometry.Scheme.sfbEtale_surjectiveClosed_module_invariance`
without changing its statement or either local-model definition. The existing
ModuleCat-valued topological-invariance API proves the actual adjunction and
constant-sheaf clauses directly. A proved private helper transports a fixed-model
isomorphism between localized and scheme etale sites. Pullback and descent of covers
retain the exact same module model, finiteness proof and finite-free splitting maps.
The DAG now distinguishes the proved etale route from the pending pro-etale plan.

Validation: the complete proof compiled through lcompile.py (5.0 seconds), then
compiled again after import pruning (4.8 seconds). The resumed sessions verified
the retained proof against the current server build (5.3 and 4.6 seconds, exit code 0).
All four public imports remain.
The resumed dry run flagged an added file-level open command. That command was
removed; pullback names inside the proof are qualified with `Limits` instead.
Only the assigned module and its node are changed; no definitions or signatures change.

## Proved and sorry left

Closed 1 of the original 2 holes:
`AlgebraicGeometry.Scheme.sfbEtale_surjectiveClosed_module_invariance`
(node `lem-sfb-surjective-closed-module-invariance`).

One original hole remains, unchanged:
`AlgebraicGeometry.Scheme.sfbProEtale_surjectiveClosed_module_invariance`
(same node). It still needs the ringed-site module adjunction lifting, its constant
module comparison, and preservation/reflection of local models on refined pro-etale
covers. The fixed-coefficient etale proof does not identify these distinct interfaces.

Added 0 holes, split off 0 statements. Both local-model definitions have zero holes.
The private helper `sfbEtale_over_model_iff` is proved. This is a proof, not a decomposition.

## No longer needed

Removed these unused proof imports from the assigned module:

- `Sheaf.AlgebraicGeometry.ProEtaleSheafTopologicalInvariance`
- `Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale`
- `Sheaf.CategoryTheory.Adjunction.LiftsGroupRingObjects`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`
- `Sheaf.Paper.PbcCompletedPullbackActual`
- `WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism`
- `WeilConjectures.AlgebraicGeometry.Sites.EtaleTopologicalInvariance`
- `Sheaf.Paper.ProEtaleSurjectiveClosedCoverRefinement`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`
- `Sheaf.AlgebraicGeometry.UniversalHomeomorphismInvariance`
- `Sheaf.AlgebraicGeometry.ProEtaleObjectInverseImageRestriction`
- `Sheaf.CategoryTheory.ConstantLeftModuleInverseImage`
- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `Sheaf.Paper.ProEtaleLocallyConstantSheafOfUniverses`
- `Sheaf.SixFunctors.GeometricInverseImageConstantModule`

The replacement proof imports are
`WeilConjectures.ConstructibleSheaf.Pullback` and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance`.

Removed from this node's proof dependencies:

- `lem-weil-pbc-etale-base-change-continuous`
- `lem-weil-pbc-etale-inverse-image-algebraic-structures`
- `lemma-weil-pbc-universal-homeomorphism-coverings`
- `prop-weil-pbc-inverse-image-modules-exact`
- `thm-weil-pbc-universal-homeomorphism-invariance`

The etale argument uses the existing generic ModuleCat-valued equivalence directly,
so it needs neither set-to-abelian-to-module lifting nor the larger cohomological
invariance theorem. Cover reflection is proved pointwise from surjectivity and the
site equivalence. The corresponding obsolete top-level tool-use approvals are removed.
Other original dependencies are retained in the node for the pending pro-etale proof;
no claim is made that those obligations have been pruned globally. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The etale part of the plan unnecessarily lifts the set-sheaf equivalence through
abelian groups to modules: the source library already states topological invariance
for arbitrary Grothendieck abelian coefficients, including ModuleCat A. Its constant
comparison also already retains every model M. The existing cover-descent proof can
be extended explicitly to retain finite-free retractions, without introducing a new
stalk-finiteness criterion or changing the local-model definition.

During validation two compile requests received no answer from the compile server;
a retry succeeded. There is no outstanding tool blocker.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
