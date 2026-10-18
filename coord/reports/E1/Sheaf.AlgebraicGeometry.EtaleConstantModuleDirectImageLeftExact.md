## What changed

Proved `AlgebraicGeometry.Etale.existsUnique_constantModuleDirectImage_leftExact` in
`Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact`, with its signature unchanged.
Constructed the scalar map by `sheafifyLift`; its factorization and uniqueness are the
sheafification universal property. The underlying-abelian-sheaf functor equality is `rfl`.
Its finite-limit preservation and reflection reduce module pushforward finite-limit
preservation to continuous abelian-sheaf pushforward. Binary-product preservation implies
additivity. Kernel preservation then transports exactness and the initial monomorphism.

Updated the node proof to describe this implementation of the same sectionwise route.
Removed the proof-only wrapper import `Sheaf.CategoryTheory.RingedSiteModules`.
No statement, definition, public import, or visibility changed. A theorem-local heartbeat
allowance covers elaboration of the large uniqueness predicate; the 60-second file timeout
is unchanged.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Etale.existsUnique_constantModuleDirectImage_leftExact`
(node `lem-weil-pbc-module-direct-image-left-exact`).
Added 0 holes; 0 holes remain in the delivered module. No split-offs or new declarations.

## No longer needed

Removed `import Sheaf.CategoryTheory.RingedSiteModules`: the proof uses Mathlib's
`SheafOfModules` directly, and the wrapper abbreviation is unused. The category-definition
node `def-weil-sheaf-of-modules-category` remains the mathematical notion used in the
statement and argument; it is not discarded. No declared proof-dependency nodes were
bypassed, and no further modules are claimed globally pruned. All public statement imports
are retained. The proof-only limits import is needed for finite-limit preservation.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The suggested pushforward adjunction does not infer
at the large site universes here; it is unnecessary. The original DAG's sectionwise argument
is implemented by preservation/reflection of finite limits through `toSheaf`, rather than
constructing tuple and kernel comparison isomorphisms separately. Additivity follows from
finite products, as permitted by the existing left-exact-additive definition node.
The scalar-map construction also covers empty schemes and zero coefficient rings: no
nonemptiness or nonzero hypothesis enters the universal property or limit argument.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
