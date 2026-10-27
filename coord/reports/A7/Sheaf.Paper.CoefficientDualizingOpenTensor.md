## What changed

Completed `AlgebraicGeometry.Etale.coefficientDualizingOpenTensor`, preserving every public
statement and definition. Added proved private helpers for the ordinary and derived mate-counit
identities, bounded flat-model transport of Tor intervals, finite common stratifications, and
open/complement homology restrictions. Updated the existing node to the implemented argument.
No other module is edited.

The coefficient map need not be flat. Exact restriction and extension preserve bounded flat
models; the existing finite scalar flat-model theorem supplies the B-coefficient interval.
Evaluation is a mate identity of the fixed adjunctions, and the ordinary equality is proved
before applying the degreewise complex functor. No inference from stalkwise equality of
arbitrary derived maps is used. The complement is explicitly retained even when empty.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.Etale.coefficientDualizingOpenTensor`
(node `lem-coef-dualizing-open-tensor`). Added zero holes; split off zero holes.
Every added private helper has a complete proof. No `sorry` remains in this module.
The proof uses the existing declared `exists_etaleScalarFlatModel`; its dependencies remain
the responsibility of their existing nodes. This is a proof from existing declarations,
not a decomposition into newly holed lemmas.

## No longer needed

Removed proof imports:

- `Sheaf.SixFunctors.EtaleOpenTensor`: evaluation follows directly from the fixed mate definitions.
- `Sheaf.SixFunctors.EtaleOpenScalarCoherence`: no separate uniqueness/normalization assertion is
  needed to identify a comparison already defined by adjunction.
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`: the source exact flat-functor API
  directly transports the bounded flat representatives.
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`: use exact `upperStar` on
  constant-module sheaves and the proved source bounded-constructible pullback lemma.
- `Sheaf.AlgebraicGeometry.OpenImmersionExtensionZeroBaseChange`: use the existing module-valued
  disjoint-range vanishing and open-adjunction unit directly, rather than its AddCommGrp theorem.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`: no independent-coefficient
  resolution is chosen in this proof.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`: the fixed scalar functor is handled
  by the stated finite scalar flat-model theorem.
- `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`: its API remains used through the
  necessary imported flat-model theory; the redundant direct import is removed.

The corresponding unused direct planned dependencies are `lem-coef-etale-open-tensor`,
`lem-coef-etale-open-scalar-coherence`, `lem-pc-kflat-resolution`,
`lem-pur-derived-change-of-rings`, `lem-pur-etale-open-derived-tensor`,
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback`,
`prop-weil-pbc-inverse-image-modules-exact`, and
`sbc-prop-extension-by-zero-and-arbitrary-base-change`.
The definition dependency `def-weil-pbc-extension-by-zero` remains in stmt_deps, rather than
being redundantly listed in proof_deps. These are direct dependency removals, not claims that
all the modules leave the target closure: some are still imported by necessary dependencies.
No library module or declaration is withdrawn.

Retained all three public imports. Added only private proof imports of the existing finite
scalar flat-model theorem, bounded constructibility, preservation of flatness, and the
constructibility comparison. `import all` accesses already proved private mate calculations
from EtaleOpenTensorDefs and EtaleProEtaleScalarMate; no private name enters a public signature
or definition body.

## Where the brief, the DAG or earlier work was wrong

Validation: the theorem header and both existing public data declarations are byte-for-byte
unchanged; all Lean lines are at most 100 characters; the updated dependency list has no
path back to this node.

No statement defect found. The planned representative-normalization route is longer than
necessary: the fixed comparisons are already defined as adjunction mates, so their counit
identity is formal. The source library already supplies the bounded flat model and
constructibility APIs needed for restriction and extension. The node records this shorter
route and the explicit finite stratification assembly. The unit route is unchanged.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
