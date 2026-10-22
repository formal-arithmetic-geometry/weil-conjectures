## What changed

Prove the specified forward graph comparison under geometric base change by constructing the
clopen graph transfer on derived categories and identifying it with the descent of the
specified sheaf graph map. The construction uses the open and closed graph section in the
compactification fibre product. Units and counits identify the transfer with the termwise
sheaf transfer on homotopy representatives; localization then identifies the comparisons.
The graph transfer commutes with base change by the pullback composition laws, the open
extension adjunction, and the proper base-change cube. Transposition and transport along
the canonical exact-functor comparison give exactly the requested forward equation.

The private graph construction follows the existing arguments in
`ClopenTransfer`, `EtaleLowerShriekCompactification`, and
`EtaleLowerShriekCompactificationBaseChange`, under
`WeilConjectures.SixFunctors.Etale.Derived`. Their public imports reach this item, so
importing those modules here would create a cycle. The private copies use only the lower
modules whose import-direction checks pass. The clopen right adjunction is constructed by
deriving the exact sheaf adjunction termwise.
Generic adjunction and diagram lemmas keep the concrete sheaf functors behind their
component formulas. The candidate unit and its adjoint transpose are constructed first for
arbitrary categories, then specialized to the derived sheaf functors. Their component
formulas avoid repeatedly expanding the concrete categorical structures. Private instances
cache the functors' additivity and exactness properties. Proper base change enters through
a private predicate, supplied by the existing torsion-ring proper base-change theorem for
finite coefficients; it introduces no assumption in the public theorem.

The theorem's signature is unchanged. All supporting constructions and proofs are private.
The private graph and normalization lemmas are proved for the coefficient category before
specializing to modules over the finite ring. This avoids repeatedly expanding the concrete
module-category structures in the kernel. Local irreducibility keeps resolution functors,
counits, and factorization isomorphisms behind their component lemmas.
No other library module or definition is changed. The added section commands and private
instances are documented for review in
`coord/changes/C4-graph-geometric-base-change-proof-context.md`; the static interface
check records a command-context difference even though public signatures stay identical.

## Proved and sorry left

Close the original hole
`AlgebraicGeometry.Etale.compactSupportGraphDerivedComparison_geometric_baseChange`.
Original holes closed: 1. Holes remaining: 0. Added holes: 0. Split off: 0.
There is no `sorry` in the delivered Lean source. The delivery command checks compilation
and preflight before pushing the packet.

## No longer needed

Removed the redundant private imports
`Sheaf.AlgebraicGeometry.ExactUnboundedExchange` and
`WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap`: both remain available
through the unchanged public import of `EtaleCompactSupportNormalizationData`.

Added private proof imports of the following derived modules:
`OpenImmersionLowerShriekProjectionBaseChange`, `EtaleLowerShriekBaseChange`,
`BaseChangeCube`, and `UpperStarIdCoherence`, all under
`WeilConjectures.SixFunctors.Etale.Derived`.

The proof avoids the high-level source theorem
`compactificationEtaleComparison_baseChange`, whose import would create a cycle through
etale localization and this item. Its low-level categorical argument is proved privately
here instead. No node or module is withdrawn. No upstream declaration is removed.

## Where the brief, the DAG or earlier work was wrong

The argument can be carried out without checking equality on geometric stalks: identify
the actual graph maps using the two clopen adjunctions and their termwise unit/counit
formulas. This avoids relying on cohomology to detect equality of derived morphisms.
The proof-dependency record now explicitly includes the existing torsion-ring proper
base-change theorem, which supplies invertibility of proper exchange.
The base-change calculation works for an arbitrary base morphism; the requested geometric
point is its specialization. Neither scheme needs to be quasi-compact or Noetherian.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
