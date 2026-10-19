## What changed

Proved `CategoryTheory.existsUnique_constantZModSheafModuleStructure` in
`Sheaf.CategoryTheory.TorsionSheafConstantModule` from the recorded Mathlib
module-sheafification construction. Construct the ZMod module on each group,
use the identity as the abelian sheafification map, and compare arbitrary
normalized actions using `Subsingleton SMulCandidate` and `Module.ext'`.
The existing annihilation, specification, and additive-morphism linearity
proofs are retained.

The constant ring coefficient universe is now `max vC uC`, the universe of
the site, while the abelian groups keep their independent universe `w`.
This makes the ring sheafification unit locally bijective by Mathlib's
concrete sheafification API. The change and its consumer check are recorded
in `coord/changes/torsion-constant-ring-universe.md`.

`Sheaf.AlgebraicGeometry.ProEtaleRootsOfUnitySheaf` has its explicit universe
argument on `constantZModRingSheaf` removed so Lean infers the site universes.
The coefficient ring there is still in universe `u + 1`.

## Proved and sorry left

Closed the one remaining hole:
`CategoryTheory.existsUnique_constantZModSheafModuleStructure`
(node `lem-pur-torsion-sheaf-constant-module`).
Holes closed: 1. Holes added: 0. No sorries remain in the item.
No statements are split off. The retained consumer modules have no sorries.
The definitions choose only from the proved uniqueness theorem.

## No longer needed

Removed redundant proof imports `Mathlib.Algebra.Module.ULift` and
`Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafify`: both are already
provided by the retained imports. No planned dependency node is pruned: the constant sheaf, sheafification,
ZMod module algebra, module-sheafification interface, and sheaf-of-modules
category are all used. No library module is withdrawn.
The abandoned `UnusedRingSheafificationLocallyBijective.lean` remains solely
in scratchpad; it is not imported or delivered.

## Where the brief, the DAG or earlier work was wrong

The previous sandbox's universe experiment had not compiled. Its proof also
needed the concrete ring limits and colimits imports, explicit dependent
module instances, identity local-bijectivity proofs, and explicit scalar
compatibility calculations. Mathlib's automatic local bijectivity of ring
sheafification uses the site universe; `HasSheafify J RingCat.{w}` alone did
not synthesize it for unrelated universes. The general mathematical site
and abelian sheaf remain arbitrary; the ambient ring universe is chosen to
fit Mathlib's construction. No target declaration is changed.

Edge cases: the proof does not use positivity except to retain the existing
signature; it also constructs the action for N = 0. For N = 1, the torsion
condition forces zero groups and the same construction applies. Empty
coverings and arbitrary site morphisms are handled by Mathlib's sheafification
construction, without nonemptiness assumptions.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
