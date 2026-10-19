## What changed

Proved `AlgebraicGeometry.Scheme.proEtaleDerivedOpenRestriction` in
`Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction`, preserving its signature and
both comparison definitions. The comparison is already the hom of the canonical
`sfProperOpenDerivedRestriction` isomorphism; its first two clauses follow directly.
For the last clause, the existing sheaf-level open-unit theorem gives full faithfulness
of extension by zero. The intrinsic pullback adjunction therefore also has invertible
unit. Exact termwise derivation, its composition comparison and identity comparison
give a derived composite isomorphic to identity. `Adjunction.isIso_unit_of_iso` proves
the unit of the specified `exceptionalOpenAdjunction` invertible, so the two whiskered
factors of the specified lambda inverse are invertible.

Updated the node proof, proof dependencies and proof origin to record this reuse of
existing constructions. The unit route is retained: restriction, exact open adjunction,
unbounded derivation and open-unit normalization. No new statements, definitions,
public imports or signatures were introduced or changed. Compilation through
`lcompile.py` is clean (4.2 seconds after proof-import pruning).

## Proved and sorry left

Closed 1 of 1 holes:
`AlgebraicGeometry.Scheme.proEtaleDerivedOpenRestriction`
(node `lem-exc-proetale-derived-open-restriction`).

Holes added: zero. Holes left in the item or added elsewhere: zero.
No decomposition or new modules.

## No longer needed

Removed these five direct proof imports:

- `Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization`
- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`

The localization and derived-composition machinery needed by the existing restriction
construction is already supplied by its defining module. The item does not separately
resolve complexes or prove independence of resolutions. Consequently the direct proof
dependencies `prop-pur-kinjective-resolutions-exist`,
`lem-weil-pbc-kinjective-total-derived`, `lem-weil-pbc-kinjective-hom-derived`, and
`def-weil-pbc-proetale-site` are no longer needed for this proof. Removed the first
three from the top-level approved `tool_uses` list; the last was not in that list.
This does not claim those nodes or modules are globally unreachable: they may remain
needed by the constructions or other consumers. Existing public statement/definition
imports remain, as do the two named, normalized comparison definitions.

## Where the brief, the DAG or earlier work was wrong

The original five-step proof plan repeated a derived-restriction construction already
present in `sfProperOpenDerivedRestriction`. Its first two conclusions are consequently
formal consequences of that definition. The substantive remaining work is the unit of
the specified derived adjunction; its invertibility follows from the sheaf open unit
and exact termwise composition, without choosing resolutions again. The proof never
uses the still-unproved proper exceptional base-change theorem in the same module as
the restriction construction, and adds no reverse dependency on its consumer.

The source item has two different sheaf adjunction presentations of restriction.
Full faithfulness of their common left adjoint transfers unit invertibility between
them; the proof does not assume their units are definitionally identical.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
