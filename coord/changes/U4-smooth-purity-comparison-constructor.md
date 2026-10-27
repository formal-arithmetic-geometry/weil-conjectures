# WeilConjectures.SmoothPurityFieldExtension.compactComparison

## Reason

Name the generic left-coordinate comparison construction as the public definition
`leftComparison`, and define the compact-support comparison by applying it.
The helper is the very same three whiskered isomorphisms as the previous body.
Keeping this constructor shared avoids repeatedly unfolding its components while
matching the adjunction, identity and cocycle equations. The generic helper is
locally irreducible after its API lemmas have been proved.

All functors, components, inverse maps and scalar associators are unchanged.
The theorem statement and every existing public declaration type are unchanged.
The new helper is a real isomorphism construction, with no postponed data.
It is attached to the existing item's node; no new proof obligation is created.

## Old

```lean
def compactComparison
    (S : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f))
    (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) :
    compactSupport D C f E ⋙ T D C E F h Y ≅
      T D C E F h X ⋙ compactSupport D C f F :=
  Functor.isoWhiskerRight (compactRealization D C f S E).symm (T D C E F h Y) ≪≫
    RationalScalarComparisonIdentification.c D C f S E F h ≪≫
      Functor.isoWhiskerLeft (T D C E F h X) (compactRealization D C f S F)
```

## New

```lean
def compactComparison
    (S : ConstructibleExceptionalCoefficients.System C.l C.Qbar D C.different (f := f))
    (E F : AdicPurityScalarNaturality.Field D C) (h : E ≤ F) :
    compactSupport D C f E ⋙ T D C E F h Y ≅
      T D C E F h X ⋙ compactSupport D C f F :=
  leftComparison (A := RCat D C E X) (B := RCat D C E Y)
    (C := RCat D C F X) (D := RCat D C F Y)
    (catA := inferInstance) (catB := inferInstance)
    (catC := inferInstance) (catD := inferInstance)
    (compactRealization D C f S E) (compactRealization D C f S F)
    (RationalScalarComparisonIdentification.c D C f S E F h)
```

## Users

The downstream/uses check for this item finds no external consumer of its
comparison. All uses are in the same item and now share the generic constructor.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SmoothPurityFieldExtension | U4 | Same comparison, expressed through its generic constructor; all transport laws are proved in the same file. |

## Status

landed 20261026T071226-L-3897322 2026-10-26 (merge of deliver/U4/Sheaf.Paper.SmoothPurityFieldExtension)
