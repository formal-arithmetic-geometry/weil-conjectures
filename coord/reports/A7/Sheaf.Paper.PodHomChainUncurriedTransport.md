## What changed

Filled `WeilConjectures.PodHomChain.uncurried_transport` in
`Sheaf.Paper.PodHomChainUncurriedTransport`, preserving its signature and all definitions.
Three proved private helpers establish raw projection naturality at all four coefficient
stages, identify the forward raw projection isomorphism, and transport the square through
the supplied tensor comparisons and full inclusion.
The main proof applies Mathlib's inverse-adjunction counit formula three times, uses tensor
and support functoriality, then substitutes the transported projection square.
No imports were added or removed. The node proof now records this argument.

## Proved and sorry left

Closed one original hole: `WeilConjectures.PodHomChain.uncurried_transport`
(node `lem-pod-hom-chain-uncurried-transport`). Added zero holes; zero holes remain
in the delivered module. All private helpers are proved. This proof uses the existing
`compactSupportProjectionFormula` dependency as intended by stage 3.

## No longer needed

No existing imports or modules were removed. The argument does not separately use
`lem-pod-hom-chain-ctf-domains` (`Sheaf.Paper.PodHomChainCtfDomains`): its domain
conditions are already encoded in the full-subcategory types. It also needs no separate
proof import or application of `fix-prop-adjunctions`
(`WeilConjectures.SixFunctors.Etale.Derived.Adjunctions`), because the restricted
adjunctions are already supplied by R. These two proof dependencies were removed from
this node's proof route only; their declarations, other users and unit routes remain.
Mathlib's general adjunction formula implements the chosen-adjunction counit clause of
`lem-pod-closed-uncurry-laws` directly, without selecting a different closed adjunction.

## Where the brief, the DAG or earlier work was wrong

No statement error found. A separate domains proof is unnecessary for this signature:
all intermediate objects already belong to the required full subcategories by construction.
The current blueprint Step 1 and the unit route are retained. No public interface or
source-library declaration was changed.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
