## What changed

Proved `AlgebraicGeometry.Etale.flatSupportChainDiagram` in
`Sheaf.AlgebraicGeometry.FlatSupportChainDiagram`. All existing declaration signatures
and definitions are unchanged. Proved private helpers establish the comparison
naturality, right square, ordinary summand adjunct, unique kernel factorization,
degreewise tensor short exactness, and naturality of both outside arrows.

The proof works first for an additive strong monoidal left adjoint between braided
monoidal closed Grothendieck abelian categories, then specializes to the given etale
adjunction. Degreewise total tensor exactness uses the discrete diagram of pairs
`p+q=n`, exactness detected by evaluations, and the exact coproduct functor. The
termwise right adjoint is never asserted to commute with coproducts.

Updated the existing node's proof, proof dependencies, proof origin and obsolete
tool approvals to describe this argument. No new public declarations or nodes.
Import cleanup is recorded in
`coord/changes/G6-flat-support-chain-diagram-imports.md`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.flatSupportChainDiagram`
(node `lem-pur-flat-support-chain-diagram`).

Initial holes: 1. Final holes: 0. Added holes: 0. Split-off statements: 0.
All private helpers have complete proofs. No other module is changed.

## No longer needed

The proof does not use
`Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`
(node `lem-pur-cochain-pullback-tensor-coherence`). Its canonical comparison is
already the strong monoidal comparison of the ordinary etale upper-star functor,
with the summand formula supplied by the existing source-library API. No general
ringed-site module pullback comparison or second coefficient action is needed.

The proof does not use
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
(node `prop-weil-pbc-inverse-image-modules-exact`). The actual adjunction, additivity
and strong monoidal instance are provided directly by the existing etale API.
These two obsolete top-level `tool_uses` entries are removed in their original order;
statement dependencies remain unchanged because the mathematical statement has not
changed. Their use elsewhere in the project is not withdrawn.

Removed the following imports (some original paths are redundant because their
APIs remain available through a retained public import):

- `WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Mathlib.Algebra.Homology.BifunctorShift`
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`
- `WeilConjectures.SixFunctors.OpenClosed.Supports`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`

The replacement imports provide the actual sheaf Grothendieck, tensor-colimit,
preadditive-complex and cochain monoidal shortcut instances. The change record
gives the exact old and new lists.
No module is withdrawn. No blueprint unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition repair was needed. The DAG's generic ringed-topos
comparison and inverse-image exactness inputs are stronger than this Lean proof
needs. The existing comparison natural transformation and tensorator inverse API
suffice. Their inverse arrows are identified by uniqueness of inverse, rather than
by definitional equality.

The short exactness clause is conditional on epic units exactly as stated. It makes
no claim that an arbitrary sheaf epimorphism is sectionwise surjective. Flatness is
used only through the given exactness of `tensorRight (Q.X p)`; braiding transfers
finite-limit preservation to tensorLeft. Zero complexes, the identity adjunction,
empty opens, non-epic units, and unbounded complexes introduce no extra hypotheses.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
