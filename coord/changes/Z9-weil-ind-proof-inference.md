# WeilIndSheafCategory proof elaboration

## Reason

The new proofs use explicit Kan-extension preservation witnesses. Three generic
backwards instance searches are disabled during their construction and restored
with their default priority after that section. Local irreducibility keeps the
chosen Kan extension and pullback functors from unfolding during proof search.
The existing statements, public imports, definitions, and final exported instance
registrations retain their signatures and meaning. The heart abelianness theorem
and its unchanged instance move after the explicit fully faithful small-pair model.

## Old

```lean
section IndExtension
universe w
variable {C B : Type w} [SmallCategory C] [SmallCategory B]
  [Abelian C] [Abelian B]
```

No local irreducibility or temporary Kan-extension instance changes were present.

## New

```lean
section IndExtension
attribute [-instance] Functor.hasLeftKanExtension_of_preserves
attribute [-instance] Functor.hasPointwiseLeftKanExtension_of_preserves
attribute [-instance] Functor.PreservesLeftKanExtension.preserves
```

After the explicit Kan-extension interface the proof uses:

```lean
attribute [local irreducible] zlIndMap zlIndMapIso
```

After the section the three original instance registrations are restored:

```lean
attribute [instance] Functor.hasLeftKanExtension_of_preserves
attribute [instance] Functor.hasPointwiseLeftKanExtension_of_preserves
attribute [instance] Functor.PreservesLeftKanExtension.preserves
attribute [local irreducible] zlIndMap zlIndMapIso
```

Inside the Frobenius-equivalence proof section only, commonStageDerivedPullback
and rationalDerivedPullback are locally irreducible. Scheme.residueField is sealed
locally to prevent instance search through stalks. No reducibility attribute is
exported. Scoped omit commands remove unused Abelian assumptions from new private
helpers. Every private helper is proved.

## Users

The read-only downstream scan found 1007 transitive consumers. Its declaration
scan found the following direct users besides this item. Proof-local commands do
not change their elaborated statements or the bodies of any public definition.
No consumer adaptation is necessary and no other group's module is edited.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.WeilIndSheafCategory | Z9 | New proofs and private helpers. |
| Sheaf.Paper.FiniteIndHeartAdjunction | unclaimed | Public Ind interface unchanged. |
| Sheaf.Paper.FiniteCompactificationWeilExact | unclaimed | Public normalized Yoneda comparison unchanged. |

No source-library declaration changes. No target statement or definition changes,
so target-meaning review does not reopen.

## Status

landed 20261025T034032-L-219411 2026-10-25 (merge of deliver/Z9/Sheaf.Paper.WeilIndSheafCategory)
