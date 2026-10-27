# finiteProperAmbientExchange

## Reason

Give the original canonical mate a shared name for use by both the operation-comparison
statement and the item, without an import cycle or repeated kernel conversion between
expanded mate terms. `finiteProperExchange` constructs precisely the original mate;
its explicit horizontal functors and square wrapper spell out the coercions in the
old construction. The original definition now aliases that construction.
The theorem signature remains verbatim. The old operation name retains its inferred
polymorphic type. The new shared module is a public import because it occurs in the body of the public definition.

## Old

```lean
noncomputable def finiteProperAmbientExchange
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' p' p g) :
    (lowerStar Λ p).rightDerivedFunctor ⋙ (upperStar Λ g).leftDerivedFunctor ⟶
      (upperStar Λ g').leftDerivedFunctor ⋙ (lowerStar Λ p').rightDerivedFunctor :=
  mateEquiv (derivedUpperStarLowerStarAdjunction Λ p)
    (derivedUpperStarLowerStarAdjunction Λ p')
    (((leftDerivedUpperStarComp Λ p' g).symm ≪≫
      eqToIso (congrArg (fun f ↦ (upperStar Λ f).leftDerivedFunctor) sq.w.symm) ≪≫
      leftDerivedUpperStarComp Λ g' p).hom)
```

## New

```lean
noncomputable abbrev finiteProperAmbientExchange := @finiteProperExchange.{u}
```

The inferred type is the original fully polymorphic type, with the same coefficient
ring, monoid structures, scheme corners, arrows and commutative-square argument.
`Sheaf.Paper.FiniteProperExchange` constructs the original mate with explicit `G`, `H`,
`TwoSquare.mk` and `.natTrans` annotations. It contains no postponed data. The former
name is an abbreviation of this construction as prescribed for duplicate definitions.
This avoids checking a second elaboration of the very large derived-module instance terms.

## Users

`python3 tools/downstream.py Sheaf.Paper.FiniteProperBaseChange --uses
finiteProperAmbientExchange` reports zero downstream modules and one module using the
name (the item itself, two textual occurrences).

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteProperBaseChange | E8 | Same definitionally equal canonical mate. |

No target statement or mathematical definition changes. No adaptation is needed.
The coefficient ring construction is unchanged.

## Status

landed 20261024T185110-L-3396084 2026-10-24 (merge of deliver/E8/Sheaf.Paper.FiniteProperBaseChange)
