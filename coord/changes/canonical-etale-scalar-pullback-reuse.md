# AlgebraicGeometry.ProEtale.scalarPullbackEtaleIso

## Reason

The existing docstring identifies this isomorphism with the published normalized
`AlgebraicGeometry.Etale.scalarPullbackIso`, but implemented a second construction
because two retired imports could not previously coexist. The current finite-
coefficient imports coexist, and the import-direction check permits the dependency.
Consolidate the duplicate canonical definitions: retain the published representative-
normalized definition and make the compatibility name an abbreviation for it.
The module is unclaimed. The existing public signatures and other definitions stay
unchanged. Add the definition's required public import and a proof-only
`import all` of the ordinary adjunction identity module for its private proof API.

The old inverse-mate expression remains a private definition. A complete private
proof `scalarPullbackEtaleIso_eq_fromMate` proves equality with it, using the ordinary
mate identity, cochain units, localization factors and uniqueness of the K-flat
normalization. No hole is added and no source-library module is changed. This is a
canonical-definition consolidation with a checked compatibility API. It removes the
need for each consumer to unfold and normalize two separate constructions.

## Old

```lean
def scalarPullbackEtaleIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pbcFixedScalarExtension Y.smallEtaleTopology a ⋙
        L(Etale.upperStar (ModuleCat.{u + 1} B) f) ≅
      L(Etale.upperStar (ModuleCat.{u + 1} A) f) ⋙
        pbcFixedScalarExtension X.smallEtaleTopology a :=
  haveI := (scalarPullbackReverse_isIso a f).2
  (asIso (scalarPullbackReverseEtale a f)).symm
```

## New

```lean
abbrev scalarPullbackEtaleIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pbcFixedScalarExtension Y.smallEtaleTopology a ⋙
        L(Etale.upperStar (ModuleCat.{u + 1} B) f) ≅
      L(Etale.upperStar (ModuleCat.{u + 1} A) f) ⋙
        pbcFixedScalarExtension X.smallEtaleTopology a :=
  Etale.scalarPullbackIso a f
```

The new private equality identifies the abbreviation with the entire old expression,
including the actual adjunction mate, not an unspecified isomorphism. The three
pre-existing proof holes of this module are unchanged.

The definition occurs in targets through the coefficient/comparison constructions.
Its implementation change reopens the semantic review of those targets. Their
statements and meanings are preserved by the proved equality with the old
construction. No hypothesis is added, removed or weakened.

## Users

The current `tools/downstream.py Sheaf.Paper.EtaleProEtaleScalarMate --uses
scalarPullbackEtaleIso` textual-use search lists only the defining module. The item
is its new explicit consumer and is adapted in the same delivery. The returned
landing at head `56a146233` additionally identified
`Sheaf.Paper.OpenRestrictionScalarExchange` as a consumer; it is explicitly covered
below even though its source is absent from the current shared tree and current
server tree (checked 2026-10-21), and it has no current claim or rework row.
Other downstream modules retain the public comparison interface.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.EtaleProEtaleScalarMate | unclaimed | Reuses the canonical definition; preserves the original mate construction via a complete proved private equality. Its existing statements and three proof holes are unchanged. |
| Sheaf.Paper.OpenRestrictionScalarExchange | unclaimed; absent from current source | Consumer named by the returned landing. No adaptation: the comparison keeps its type and its new value is proved equal to the old inverse-mate construction by scalarPullbackEtaleIso_eq_fromMate. Thus its comparison formulas retain their meaning. No absent source is recreated or withdrawn. |
| Sheaf.Paper.FiniteCoefficientDirectImage | C4 | Uses the common definition in the projection proof and the private compatibility equality in the mate and coefficient-chain calculations. All original public headers and definitions stay unchanged. |

No module held by another group is adapted.

## Status

landed 20261020T233102-L-892381 2026-10-20 (merge of deliver/C4/Sheaf.Paper.FiniteCoefficientDirectImage)
