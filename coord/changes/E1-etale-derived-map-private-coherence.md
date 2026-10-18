# AlgebraicGeometry.Etale.derivedMapRestriction_laws

## Reason

The original hole is proved using private derived-functor coherence lemmas. Static
preflight flags the additional `universe`, `open`, `variable`, and local `attribute`
commands, so this record documents their scope and consumer check. No existing public
signature, universe parameter, definition body, or visibility changes.

## Old

The original public theorem signature is:

```lean
theorem derivedMapRestriction_laws
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (∀ (U : X.Etale) (a), restrictDerivedMap B (K := K) (L := L) (𝟙 U) a = a) ∧
    (∀ (U V W : X.Etale) (f : U ⟶ V) (g : V ⟶ W) (a),
      restrictDerivedMap B (K := K) (L := L) (f ≫ g) a =
        restrictDerivedMap B f (restrictDerivedMap B g a)) ∧
    (∀ (U : X.Etale) (a), restrictDerivedIso B (K := K) (L := L) (𝟙 U) a = a) ∧
    (∀ (U V W : X.Etale) (f : U ⟶ V) (g : V ⟶ W) (a),
      restrictDerivedIso B (K := K) (L := L) (f ≫ g) a =
        restrictDerivedIso B f (restrictDerivedIso B g a))
```

The original module opens `CategoryTheory Opposite` and declares `universe u`.

## New

The public theorem has exactly the same signature:

```lean
theorem derivedMapRestriction_laws
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (∀ (U : X.Etale) (a), restrictDerivedMap B (K := K) (L := L) (𝟙 U) a = a) ∧
    (∀ (U V W : X.Etale) (f : U ⟶ V) (g : V ⟶ W) (a),
      restrictDerivedMap B (K := K) (L := L) (f ≫ g) a =
        restrictDerivedMap B f (restrictDerivedMap B g a)) ∧
    (∀ (U : X.Etale) (a), restrictDerivedIso B (K := K) (L := L) (𝟙 U) a = a) ∧
    (∀ (U V W : X.Etale) (f : U ⟶ V) (g : V ⟶ W) (a),
      restrictDerivedIso B (K := K) (L := L) (f ≫ g) a =
        restrictDerivedIso B f (restrictDerivedIso B g a))
```

Only its proof changes. All new declarations are private and proved, or private explicit
comparison constructions. The additional proof-support commands are:

```lean
universe u u'
open CategoryTheory.Limits
attribute [local irreducible] upperStar upperStarComp upperStarId
```

The extra universe is used by private helpers with general coefficient categories.
Additional `variable` commands occur only in the named sections `ExactFunctors`,
`ExactAssociativity`, `ExactIdentity`, and `PullbackCoherence`; each section ends before
the public presheaf declarations. The local irreducibility attribute prevents expensive
reduction of etale pullback constructions while checking the proof; it does not persist
in importers. The original public definitions before and after these helpers are
unchanged. `WeilConjectures.SixFunctors.BaseChange.Pasting` is a proof-only import.

## Users

`tools/downstream.py` lists only the following consumer. It uses `derivedHomPresheaf`
and `derivedIsoPresheaf`, whose types and definition bodies remain unchanged. No file
other than the item module is adapted. The queue records no holder for this consumer.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FiniteRingDerivedLocalConstancy | - in coord/queue.tsv | No source change; compiled unchanged against the proved module. |

## Status

landed 20261018T062730-L-641960 2026-10-18 (merge of deliver/E1/Sheaf.AlgebraicGeometry.EtaleDerivedMapPresheaves)
