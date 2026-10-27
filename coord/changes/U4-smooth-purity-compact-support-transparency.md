# WeilConjectures.SmoothPurityFieldExtension.compactSupport

## Reason

The raw compact-support expression is a large functor construction. Unfolding it
while elaborating the coefficient-adjunction equations contributes unnecessary
work. An abbreviation is permanently reducible and Lean refuses the ordinary
local irreducibility annotation for it. Use a definition with exactly the same
type and body, and mark it locally irreducible while proving the equations.
The existing compactRealization proof explicitly unfolds compactSupport already.

The underlying object and map actions are unchanged. This changes transparency,
not the mathematical definition or any target's meaning. No source-library file
is changed. The published theorem statement remains verbatim.

## Old

```lean
abbrev compactSupport (E : AdicPurityScalarNaturality.Field D C) :
    RCat D C E X ⥤ RCat D C E Y :=
  sfCompactSupportFiniteFunctor C.l D.k
    (PurCompactSupport.coefficientPrimeUnit C.l D C.different)
    (integralExceptionalCompactification D f) E.val
```

## New

```lean
def compactSupport (E : AdicPurityScalarNaturality.Field D C) :
    RCat D C E X ⥤ RCat D C E Y :=
  sfCompactSupportFiniteFunctor C.l D.k
    (PurCompactSupport.coefficientPrimeUnit C.l D C.different)
    (integralExceptionalCompactification D f) E.val
```

## Users

`tools/downstream.py Sheaf.Paper.SmoothPurityFieldExtension --uses
WeilConjectures.SmoothPurityFieldExtension.compactSupport` reports zero downstream
modules and only the item itself as a textual user. A direct search of both Lean
roots finds no qualified or open-namespace consumer outside the item.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SmoothPurityFieldExtension | U4 | The same body is a definition; local irreducibility avoids unfolding it in the new proof. Its explicit realization proof is unchanged. |

There are no forced adaptations.

## Status

landed 20261026T071226-L-3897322 2026-10-26 (merge of deliver/U4/Sheaf.Paper.SmoothPurityFieldExtension)
