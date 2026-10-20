## What changed

Replaced the assigned projection/exchange hole by the fixed-coefficient pro-etale
adjunction calculation. The public theorem statement is unchanged. The argument proves the
proper factor by the general right-adjoint projection/mate identity, proves the open factor
by its unit identity and the general projection/mate identity, and pastes the two squares
using pullback associativity. It specializes the calculation to finite module coefficients
with an explicit identification of the coefficient braiding instances.

All supporting declarations are private. Their data are the existing canonical functors,
isomorphisms and natural transformations, and their proofs are complete. The etale source
calculation supplies a proof template; the proof applies pro-etale operations throughout.
The unit's proper/open factorization route is preserved.

The change record is
`coord/changes/T2-compactification-projection-exchange-proof-scopes.md`.

## Proved and sorry left

Closed the module's one original hole:
`AlgebraicGeometry.ProEtale.compactification_projection_exchange_coherence`
(node `lem-pur-co-smooth-pf-exchange-coherence`). Holes closed: 1; holes added: 0;
remaining holes in delivered Lean files: 0; split statements: 0.

The final ordered build compiled the module in 30.0 seconds, then checked its axioms
and compiled its unchanged direct consumer, `Sheaf.Paper.CohomologicalSmoothComposition`,
in 9.5 seconds against the freshly built module. The axiom audit lists only `propext`,
`Classical.choice` and `Quot.sound`. No delivered declaration contains a hole.

## No longer needed

The following original proof imports are removed:

- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition`
- `Sheaf.Paper.RingedExchangeTensorCoherence`
- `Sheaf.Paper.ProjectionMateExact`
- `Sheaf.Paper.IntegralFinitePullbackComposition`
- `Sheaf.SixFunctors.OpenTensorNormalization`

The following public imports supplied no names required by the theorem's statement or the
new proof and are removed:

- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare`
- `Sheaf.AlgebraicGeometry.ProEtaleFiniteModules`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`
- `Sheaf.SixFunctors.IntrinsicDerivedTensor`
- `Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero`

This proof does not use the following old proof dependencies, and removes their obsolete
entries from this node's top-level `tool_uses` list:

- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`: the published fixed-coefficient tensor
  comparison is the general derived comparison already proved in the source library.
- `lem-weil-pbc-proetale-derived-pullback-composition`: the source library's proved
  fixed-coefficient associativity theorem gives the needed composition coherence.
- `lem-sf-open-tensor-normalization`: the open unit identity and the canonical tensor
  comparisons give the needed square directly.
- `lem-weil-pbc-ringed-exchange-tensor-coherence`: the general adjunction projection/mate
  theorem applies directly to the published fixed-coefficient maps.
- `lem-weil-pbc-ringed-projection-mate-exact`: naturality of the existing natural
  transformations provides the required naturality equations.

These modules and nodes are unnecessary for this item's proof. No source-library
statement or file is withdrawn, and no claim is made that other proofs no longer use them.

## Where the brief, the DAG or earlier work was wrong

The old plan used general ringed-module presentations whose interfaces do not directly
identify all the fixed-coefficient maps in this theorem. The adopted source library already
contains the relevant general categorical identities and a complete etale calculation with
the same proper/open factorization. Applying those identities to the pro-etale adjunctions
avoids the presentation transports. No mathematical statement is weakened or disputed.

## Second reading by T2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
