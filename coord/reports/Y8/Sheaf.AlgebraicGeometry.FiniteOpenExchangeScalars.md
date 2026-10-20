## What changed

Completed the two remaining proofs in
`Sheaf.AlgebraicGeometry.FiniteOpenExchangeScalars`, preserving all public signatures
and definitions. The open scalar mate is transported twice through the proved
fixed-scalar equivalences, reducing invertibility to the existing extension-by-zero
scalar comparison. Pullback-compositor coherence supplies the right-adjoint cube for the exchanges.
A third application of the mate cube identity proves compatibility of the normalized
inverse exchanges; inversion gives the complex-level exchange.

Reused the ring-sheaf module's proved `restrictionPullback_mate` through a private
`import all`, replacing a duplicated expanded proof. Naturality and coefficient
composition use general mate and isomorphism lemmas
in the sheaf categories, with explicit category and functor parameters. Their
complex-level equalities are checked degreewise on sections. Private equations
for the scalar-model comparisons and Mathlib's complex-component API keep the
proofs from unfolding the large adjunction constructions. The strict and ambient
tower proofs now check successor squares degreewise on sections; the proved
identity-on-sections equation for `ambientRes` supplies the ambient comparison.

Added only proved private helpers and private proof imports. Updated the existing
node's proof, proof dependencies, and proof origin to describe these arguments.
No other library module is changed. The command-scope changes and consumer audit
are recorded in `coord/changes/Y8-finite-open-exchange-proof-scopes.md`. The complete
file compiled in 50.8 seconds, and the delivery compilation and axiom probe passed.

## Proved and sorry left

Closed both original holes:

- `AlgebraicGeometry.ProEtale.StrictTower.FiniteOpenScalars.openResMap_isIso`.
- `AlgebraicGeometry.ProEtale.StrictTower.FiniteOpenScalars.exchange_restrictScalars`.

The item has zero remaining holes; no holes or split statements are added.
Both declarations belong to `lem-cbc-finite-open-exchange-scalars`.

## No longer needed

The former private `mate_unit_iso` is replaced by the proved
`mate_unit_counit_iso` API, which accepts the established mate equation and
supplies both unit and counit identities.

Removed the direct proof imports of `ProEtaleConstantExact`,
`ProEtaleDerivedExtensionZeroBaseChange`, `ProEtaleInverseImage`,
`WeilConjectures.CategoryTheory.ExtensionByZeroPresheaf`, and
`WeilConjectures.CategoryTheory.SiteMorphismComposition`. Their declarations remain
in the library and some remain transitive dependencies. No module or DAG node is
withdrawn. `def-weil-extension-by-zero-presheaf` and
`def-weil-presheaf-modules-sheafification` remain statement dependencies, but
are no longer direct dependencies of this node's proof.

## Where the brief, the DAG or earlier work was wrong

No false statement or target change was needed. The summand-level description in
the earlier plan required an explicit bridge to the chosen ring-sheaf module
adjunctions. Two applications of the mate cube identity provide that bridge.
The inverse exchange is itself an inverse mate of the square compositor. Its
coefficient compatibility follows from the same cube identity, once compositor
coherence and the recorded unit normalization are established.

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
