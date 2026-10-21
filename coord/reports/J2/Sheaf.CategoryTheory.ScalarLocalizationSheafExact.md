## What changed

Proved `CategoryTheory.scalarLocalization_sheaf_exact` in the assigned module without changing
its signature, public imports, or definitions used by targets. Added only proved private
helpers: sectionwise flat tensor preserves finite limits; exact monoidal sheafification
transfers this property to sheaves; the specified scalar-extension objects and maps form a
functor; and its underlying abelian-sheaf functor agrees naturally with tensoring by the
restricted localized ring. Faithful exact forgetful functors reflect the resulting
preservation properties. The final clause transports them along any natural isomorphism.

The node copy records this implementation.
`coord/changes/scalar-localization-sheaf-exact-proof-scope.md` records the added scope commands
that the static interface checker classifies as visible; there are no downstream importers. The module compiles cleanly through `lcompile.py`
in 33.1 seconds after pruning proof imports. The proof uses neither enough points nor
surjectivity of sections of an epimorphism, and includes nilpotent sections, zero rings and
empty finite diagrams.

## Proved and sorry left

Closed 1 of 1 original holes: `CategoryTheory.scalarLocalization_sheaf_exact`
(node `lem-weil-pbc-scalar-localization-sheaf-exact`). Added 0 holes. No `sorry` remains in
any delivered Lean file. No statements were split off.

## No longer needed

Removed proof imports:

- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`
- `Mathlib.RingTheory.Flat.Basic` (provided by the new categorical flatness import)
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal` (already publicly available)
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification` (already publicly available)
- `Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings` (already publicly available)

The proof does not call `lem-pc-sites-modules-sheafification-flat`: its upstream signature
identifies the site and coefficient universes, while this item keeps them independent.
Instead a private helper proves precisely the needed special case from exact monoidal
sheafification and its adjunction. The proof does not use `def-pc-flat-sheaf-modules` or the
closedness theorem `lem-pc-sheaf-modules-tensor-closed`; the existing independent-universe
tensor instances supply symmetry, additivity and finite-colimit preservation. Removed these
three node dependencies and the two obsolete `tool_uses` entries. No library module is
withdrawn, and no claim is made that other consumers no longer need those modules.

## Where the brief, the DAG or earlier work was wrong

The mathematics and statement are unchanged. The stated sheafification-flat and tensor-closed
interfaces have fixed site universes, so they cannot be applied directly to this statement.
The existing independent-universe monoidal localization API supplies the required comparisons,
and the private proof of the sheafification step avoids any interface repair. No changes to
other modules or new nodes are needed. The first preflight requested a change record for the
added `open` and section-variable commands; that record now documents their effect and the
zero downstream-module consumer check.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
