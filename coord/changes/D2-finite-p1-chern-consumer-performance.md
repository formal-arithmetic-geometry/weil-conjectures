# finiteP1_kummer_chern_realization

## Reason

The unchanged consumer exceeded the 60-second file limit while validating the
coordinate-definition relocation: 79.9 seconds against the delivery. Profiling
also found the original slow against published dependencies (61.7 seconds).
About 50 seconds were spent in linting the proof's large `simpa` conversions.
Replace the two conversion steps by explicit unfolding followed by `exact`.
The profiled adaptation compiles in 14.7 seconds, with linting down to 7.4 seconds.
No signature, definition, instance, attribute, visibility, public import, target
meaning, or proof dependency changes. No target statement review is reopened.
The module was unclaimed in the current coordination state when edited.

## Old

```lean
theorem finiteP1_kummer_chern_realization
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (e : X ≅ ProjectiveLine S) (cX : Chern l E X)
    (hc : FiniteChernNormalization l E cX)
    (hS : IsUnit (l : Γ(S, ⊤))) (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    {hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n X hX) :
    ∃ t : (SpTowerShriek.Ev l E X n).obj ((line l E cX)⟦(2 : ℤ)⟧) ≅
      (finiteOverRealization l E n e).obj
        (geoP1Twist (FiniteRing l E n) (l ^ (n + 1))
          (ULift.ext _ _ (coefficient_annihilates l E n)) (ProjectiveLine S) 1 2),
      (SpTowerShriek.Ev l E X n).map
          (firstChern l E cX (Scheme.Pic.mapHom e.hom (hyperplanePic S))) ≫ t.hom =
        (finiteOverUnitCoordinate l E n e c).hom ≫
          (finiteOverRealization l E n e).map (finiteP1PositiveClass l E S hS n) := by
  obtain ⟨t⟩ := finiteP1_kummer_comparison_iso l E e cX hS n c
  have hb : FiniteP1BoundaryData l E e cX n := by
    simpa only [FiniteP1BoundaryData] using
      hc (Scheme.Pic.mapHom e.hom (hyperplanePic S)) n
  have h := finiteP1_kummer_chern_realization_of_boundary l E e cX hS n c t hb
  exact ⟨t, by simpa only [finiteP1PositiveClass] using h⟩
```

## New

```lean
theorem finiteP1_kummer_chern_realization
    {X S : Scheme.{u}} [IsNoetherian X] [IsNoetherian S]
    (e : X ≅ ProjectiveLine S) (cX : Chern l E X)
    (hc : FiniteChernNormalization l E cX)
    (hS : IsUnit (l : Γ(S, ⊤))) (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    {hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n X hX) :
    ∃ t : (SpTowerShriek.Ev l E X n).obj ((line l E cX)⟦(2 : ℤ)⟧) ≅
      (finiteOverRealization l E n e).obj
        (geoP1Twist (FiniteRing l E n) (l ^ (n + 1))
          (ULift.ext _ _ (coefficient_annihilates l E n)) (ProjectiveLine S) 1 2),
      (SpTowerShriek.Ev l E X n).map
          (firstChern l E cX (Scheme.Pic.mapHom e.hom (hyperplanePic S))) ≫ t.hom =
        (finiteOverUnitCoordinate l E n e c).hom ≫
          (finiteOverRealization l E n e).map (finiteP1PositiveClass l E S hS n) := by
  obtain ⟨t⟩ := finiteP1_kummer_comparison_iso l E e cX hS n c
  have hb : FiniteP1BoundaryData l E e cX n := by
    unfold FiniteP1BoundaryData
    exact hc (Scheme.Pic.mapHom e.hom (hyperplanePic S)) n
  have h := finiteP1_kummer_chern_realization_of_boundary l E e cX hS n c t hb
  refine ⟨t, ?_⟩
  unfold finiteP1PositiveClass
  exact h
```

## Users

`downstream.py --uses finiteP1_kummer_chern_realization` gives the declaration's
own module and its one caller. That caller is also the only direct importer.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteP1KummerChernRealization | unclaimed | Only the two terminal conversion steps change; same statement and dependency route. |
| Sheaf.Paper.DiagonalTraceFiniteChernComparison | unclaimed | Same signatures and attributes; compiled against the adaptation without changing it. |

## Status

withdrawn

Withdrawn by the reviewer (2026-10-28). The adaptation is not forced. The unchanged
original `Sheaf.Paper.FiniteP1KummerChernRealization` compiles cleanly against the delivered
modules in 48.5 s, and against the published build in 45.9 s, in the same run (both under
the 60 s limit; the adapted text took 16.6 s). The same claim was withdrawn in the T7
delivery of this item (8784ba11). The module is restored byte for byte to its published
text. D3 is also changing its dependency `FiniteP1KummerBoundaryTransport` (∀ t → ∃ t), so
any adaptation of this consumer belongs to that repair.
