# condensedCoefficientCoherence

## Reason

The completed coherence proof needs the canonical module-category structures repeatedly.
Constructing them after substituting concrete coefficient rings exceeded the 60-second
single-file limit. Private helpers package these same instances over abstract rings, and
private derived-scalar coherence helpers specialize the existing proved transport lemmas.
A fully proved generic `scalarCalculus` lemma also shares the unchanged exact coefficient
calculus argument between its two concrete specializations.
The static checker observes new local attributes and generic variable commands. They do
not change the public interface: instance registration is confined to `ModuleCacheScope`,
which ends before any public theorem. Generic helpers receive the chosen derived categories
explicitly, and public proof bodies introduce the canonical data caches locally.
No public signature, definition, public import, or visibility changes. Proof-only imports
are pruned or strengthened to `import all` as described below.

## Old

```lean
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.CommShift.ofIso CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
```

`AlgebraicGeometry.ProEtale.condensedCoefficientCoherence` had proof `by sorry`.
The public signatures of all four existing theorems are unchanged.

## New

```lean
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctorIsoMapDerivedCategory
  CategoryTheory.Functor.CommShift.ofIso CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Mod.extendScalars
```

`ModuleCacheScope` contains private canonical module-structure helpers and local instance
registrations, followed by the existing coherence tools and new proved private scalar-derived
coherence helpers. The scope ends before `AlgebraicGeometry.ProEtale` and its public
signatures. The finite and closure calculus proofs apply the fully proved generic
`scalarCalculus`;
the private helpers accept the chosen derived categories explicitly. Public proof bodies
introduce the private canonical data caches with `let :=`, without changing their signatures.
`condensedCoefficientCoherence` has a complete proof of all eight clauses.

The proof-only `MapMod` and `FunctorCategory.Complete` imports are removed. The existing
source Compatibility module is imported with `import all`, so its private proved
`continuousBasisSheafIso` and `mapFreeRestrictedRegularIso` can replace duplicated local
constructions. These source private names occur only in proof bodies. No source module
is changed.

## Users

`tools/downstream.py Sheaf.Paper.CondensedFlatCoefficientCalculus --names` lists these six
modules. They see the identical public declarations, definitions, public imports, and instances.
No user is adapted.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CondensedQbarBaseChangeCompatibility | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.CondensedQbarExchangeEquality | A3 | Same public interface; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | A2 | Same public interface; no adaptation. |
| TargetsCheck | unclaimed | Same public interface; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Same public interface; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Same public interface; no adaptation. |

## Status

landed 20261016T054836-L-157364 2026-10-16 (merge of deliver/G2/Sheaf.Paper.CondensedFlatCoefficientCalculus)
