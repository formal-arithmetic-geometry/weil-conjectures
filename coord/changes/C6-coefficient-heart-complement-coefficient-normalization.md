# AlgebraicGeometry.ProEtale.coefficientHeart_curve_complement

## Reason

The bundled coefficient argument forces the consumer to compare the monoid structure
on `(Mon.mk Λ).X` with the already supplied structure on `Λ`. Its localization clause
then unfolds large pullback and adjunction constructions; an isolated consumer hits
a kernel deterministic timeout. State the theorem over the actual sheaf with its
monoid and commutativity instances, as the existing coefficient-module APIs do.
This is the same mathematical statement: a bundled commutative condensed ring is
exactly a condensed abelian sheaf with these structures. No hypothesis or conclusion
is changed, and the existing complete proof is retained with `Λ.X` replaced by `Λ`.
The module is unclaimed. No existing source declaration consumer was found.

## Old

```lean
theorem coefficientHeart_curve_complement
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X]
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (hdim : topologicalKrullDim X ≤ 1) (U : X.Opens)
    (hU : ∀ C ∈ irreducibleComponents X, ∀ η : X, IsGenericPoint η C → η ∈ U)
    (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsReduced Z]
    (hi : Set.range i = (U : Set X)ᶜ)
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ.X X)) :
    topologicalKrullDim Z ≤ 0 ∧
    Finite Z ∧
    (∀ z : Z, IsClosed ({i z} : Set X)) ∧
    Mono ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ.X U.ι).counit.app F) ∧
    Epi ((CondensedRing.upperStarLowerStarAdjunction Λ.X i).unit.app F) ∧
    (ComposableArrows.mk₂
      ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ.X U.ι).counit.app F)
      ((CondensedRing.upperStarLowerStarAdjunction Λ.X i).unit.app F)).Exact ∧
    IsZero ((CondensedRing.upperStar Λ.X U.ι).obj
      ((CondensedRing.lowerStar Λ.X i).obj ((CondensedRing.upperStar Λ.X i).obj F)))
```

## New

```lean
theorem coefficientHeart_curve_complement
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u}) [IsLocallyNoetherian X] [CompactSpace X]
    (hdim : topologicalKrullDim X ≤ 1) (U : X.Opens)
    (hU : ∀ C ∈ irreducibleComponents X, ∀ η : X, IsGenericPoint η C → η ∈ U)
    (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i] [IsReduced Z]
    (hi : Set.range i = (U : Set X)ᶜ)
    (F : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) :
    topologicalKrullDim Z ≤ 0 ∧
    Finite Z ∧
    (∀ z : Z, IsClosed ({i z} : Set X)) ∧
    Mono ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ U.ι).counit.app F) ∧
    Epi ((CondensedRing.upperStarLowerStarAdjunction Λ i).unit.app F) ∧
    (ComposableArrows.mk₂
      ((CondensedRing.openImmersionLowerShriekUpperStarAdjunction Λ U.ι).counit.app F)
      ((CondensedRing.upperStarLowerStarAdjunction Λ i).unit.app F)).Exact ∧
    IsZero ((CondensedRing.upperStar Λ U.ι).obj
      ((CondensedRing.lowerStar Λ i).obj ((CondensedRing.upperStar Λ i).obj F)))
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.CoefficientHeartCurveComplement | unclaimed | Coefficient argument unbundled; complete proof retained. |
| Sheaf.Paper.CoefficientHeart | C6 | Pass the coefficient sheaf directly, preserving the target signature. |

`tools/downstream.py Sheaf.Paper.CoefficientHeartCurveComplement --uses
coefficientHeart_curve_complement` reports zero current importers and only the
declaration itself as a textual occurrence. The assigned parent's previously
unfinished proof is the new consumer.

## Status

landed 20261024T204534-L-3791332 2026-10-24 (merge of deliver/C6/Sheaf.Paper.CoefficientHeart)
