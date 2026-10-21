## What changed

Filled `SheafOfModules.SubterminalLocal.subterminal_module_local_calculus` in
`Sheaf.CategoryTheory.SubterminalModuleLocalCalculus`. Every existing public definition and the
complete theorem signature remain verbatim. Added proved private helpers and private proof imports.
The six helper typeclass registrations are local to `section LocalCalculusProof`; no global
instance is added. The conservative section-command preflight request is documented in
`coord/changes/u8-subterminal-local-proof-scope.md`.

The proof constructs slice extension as global extension followed by restriction. Its adjunction
comes from the standard restriction/pushforward adjunction and subterminality. The intersection
exchange is the inverse mate of the canonical restriction square. Its invertibility follows by
mating again: the resulting component is restriction along the explicit slice isomorphism
`Y ×_V W ≅ U × Y`. Adjunction uniqueness and the mate identities establish all prescribed units,
counits, composition comparisons and nested-map equations.

The remaining clauses use singleton direct sums, a universe-independent proof of the normalized
sheafification comparison, cover separatedness, exact-functor homology and the existing proved
source-library derived homology comparison. Updated the node's proof, proof dependencies and
proof origin to match this route.

## Proved and sorry left

Closed the original one hole:
`SheafOfModules.SubterminalLocal.subterminal_module_local_calculus`
(node `lem-sp-subterminal-module-local-calculus`). All private helpers are proved.

Holes closed: 1. Holes added: 0. Holes remaining: 0. No statements were split off.
The public definitions and theorem signature were compared with the repository source and match.
`lcompile.py` compiled the final packet in 36.9 seconds with exit code 0 and no warnings.
A separate `#print axioms` compile passed in 28.9 seconds and reported exactly `propext`,
`Classical.choice` and `Quot.sound` for the completed main theorem.

## No longer needed

Removed the original private import `Sheaf.CategoryTheory.ModuleSheafificationRestriction`.
The dependency `lem-weil-pbc-module-sheafification-restriction` and its obsolete `tool_uses` entry
are removed from this node: the needed independent-universe comparison is proved privately from
Mathlib's locally bijective morphisms and module sheafification localization. A direct import-closure comparison also removes
`Sheaf.CategoryTheory.ModuleSheafificationLocalIso`
(node `lem-weil-pbc-module-sheafification-local-iso`) from this item's imports.
Neither module nor any declaration is withdrawn; other consumers may still need them.

No separate direct-sum construction of the intersection exchange is needed: the iterated mate
and the product/pullback isomorphism prove it. The explicit extension-presheaf definition,
module-sheafification definition, localized adjunction and the three existing Mathlib leaves for
exact homology, complex cohomology and triangulated derived functors remain dependencies.
No Lean module is deleted and no blueprint unit is bypassed.

## Where the brief, the DAG or earlier work was wrong

The named sheafification-restriction theorem is stated with one common universe for small sites.
It cannot directly instantiate this item's independent site, hom and coefficient universes.
The same proof works in the required universes and is included as proved private helpers.
The original intersection and nested-map plan is correct, but a categorical mate argument avoids
repeating the presheaf generator calculation for all normalization diagrams.

Preflight initially requested this change record for proof-scope commands and registrations.
The top-level extra open was removed, the elaboration option was scoped, and all helper
registrations were changed to local attributes on private proved theorems. No consumer needed
adaptation and the public API remains unchanged.

## Second reading by U8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
