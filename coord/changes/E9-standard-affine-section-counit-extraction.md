# AlgebraicGeometry.Etale.sectionCoordinateCounit_standard

## Reason

The existing standard affine case was in SectionCoordinateCounitNormalization, which
imports SectionCoordinateOrientationSquare for its centred-chart conclusion. Reusing the
standard case in the latter would form an import cycle. The parent is unclaimed in the
current shared claim records. Extract only the existing standard assertion to
Sheaf.Paper.StandardAffineSectionOrientation, preserving its name, binders, universes,
conclusion and sorry proof. The new module also proves the fixed-presentation version
by normalization uniqueness and source-orientation cancellation. The original parent
publicly imports the new module, preserving the availability of the original declaration.
No adopted source-library module is changed.

## Old

In Sheaf.Paper.SectionCoordinateCounitNormalization:

```lean
theorem sectionCoordinateCounit_standard (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    ∃ (adjC : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin d)) S ↘ S) ⊣ affineRight A N hA S d)
      (adjF : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin d)) (AffineSpace (ULift.{u} (Fin 1)) S) ↘ _) ⊣
          affineRight A N hA (AffineSpace (ULift.{u} (Fin 1)) S) d),
      CoordinateCounitArrows.IsNormalized N hN A hA t D S hS d adjC ∧
      @CoordinateCounitArrows.IsNormalized N hN A _ _ hA t D
        (AffineSpace (ULift.{u} (Fin 1)) S)
        (noetherianSource (AffineSpace (ULift.{u} (Fin 1)) S ↘ S))
        (invertibleOnSource N (AffineSpace (ULift.{u} (Fin 1)) S ↘ S) hS) d adjF ∧
      (restrictionAtOne A S
        (rawComparison A N hN hA S hS d _ _
          (affineSectionIso A N hN hA S hS d
            (AffineSpace.zeroSection (ULift.{u} (Fin d)) S) adjC)
          (@affineSectionIso A _ _ N hN hA (AffineSpace (ULift.{u} (Fin 1)) S)
            (noetherianSource (AffineSpace (ULift.{u} (Fin 1)) S ↘ S))
            (invertibleOnSource N (AffineSpace (ULift.{u} (Fin 1)) S ↘ S) hS) d
            (AffineSpace.zeroSection (ULift.{u} (Fin d)) _) adjF))).hom =
        sectionMap A
          (AffineSpace (ULift.{u} (Fin d)) (AffineSpace (ULift.{u} (Fin 1)) S) ↘ _)
          (AffineSpace (ULift.{u} (Fin d)) S ↘ S)
          (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
          (AffineSpace.map (ULift.{u} (Fin d))
            (AffineSpace.oneSection (ULift.{u} (Fin 1)) S))
          (AffineSpace.isPullback_map _)
          (AffineSpace.zeroSection (ULift.{u} (Fin d)) _)
          (AffineSpace.zeroSection (ULift.{u} (Fin d)) S)
          (AffineSpace.zeroSection_comp_map _)
```

Proof: `by sorry`.

## New

The identical declaration is in Sheaf.Paper.StandardAffineSectionOrientation:

```lean
theorem sectionCoordinateCounit_standard (N : ℕ) (hN : 0 < N)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    (D : ∀ (T : Scheme.{u}) [IsNoetherian T] (hT : IsUnit (N : Γ(T, ⊤))),
      OrdinaryFiniteP1Datum A N hA t T hT)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) (d : ℕ) :
    ∃ (adjC : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin d)) S ↘ S) ⊣ affineRight A N hA S d)
      (adjF : rightDerivedLowerShriek (ModuleCat.{u + 1} A)
        (AffineSpace (ULift.{u} (Fin d)) (AffineSpace (ULift.{u} (Fin 1)) S) ↘ _) ⊣
          affineRight A N hA (AffineSpace (ULift.{u} (Fin 1)) S) d),
      CoordinateCounitArrows.IsNormalized N hN A hA t D S hS d adjC ∧
      @CoordinateCounitArrows.IsNormalized N hN A _ _ hA t D
        (AffineSpace (ULift.{u} (Fin 1)) S)
        (noetherianSource (AffineSpace (ULift.{u} (Fin 1)) S ↘ S))
        (invertibleOnSource N (AffineSpace (ULift.{u} (Fin 1)) S ↘ S) hS) d adjF ∧
      (restrictionAtOne A S
        (rawComparison A N hN hA S hS d _ _
          (affineSectionIso A N hN hA S hS d
            (AffineSpace.zeroSection (ULift.{u} (Fin d)) S) adjC)
          (@affineSectionIso A _ _ N hN hA (AffineSpace (ULift.{u} (Fin 1)) S)
            (noetherianSource (AffineSpace (ULift.{u} (Fin 1)) S ↘ S))
            (invertibleOnSource N (AffineSpace (ULift.{u} (Fin 1)) S ↘ S) hS) d
            (AffineSpace.zeroSection (ULift.{u} (Fin d)) _) adjF))).hom =
        sectionMap A
          (AffineSpace (ULift.{u} (Fin d)) (AffineSpace (ULift.{u} (Fin 1)) S) ↘ _)
          (AffineSpace (ULift.{u} (Fin d)) S ↘ S)
          (AffineSpace.oneSection (ULift.{u} (Fin 1)) S)
          (AffineSpace.map (ULift.{u} (Fin d))
            (AffineSpace.oneSection (ULift.{u} (Fin 1)) S))
          (AffineSpace.isPullback_map _)
          (AffineSpace.zeroSection (ULift.{u} (Fin d)) _)
          (AffineSpace.zeroSection (ULift.{u} (Fin d)) S)
          (AffineSpace.zeroSection_comp_map _)
```

Proof: `by sorry`, unchanged. The original parent adds:

```lean
public import Sheaf.Paper.StandardAffineSectionOrientation
```

Its existing node drops only this declaration from lean.declarations and reuses the
new owning node lem-trf-standard-affine-section-orientation in its standard-case proof
step. The main declaration and every other existing signature and definition stay
identical. The theorem has been moved, not closed or duplicated.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SectionCoordinateCounitNormalization | unclaimed | Declaration exported by the new public import; remaining proofs and signatures unchanged. |
| Sheaf.Paper.AffineDiagonalTraceRestriction | unclaimed | Direct importer; public declarations retained; compiled against the packet. |
| Sheaf.Paper.AffineDiagonalIntegrationOrientation | unclaimed | Transitive importer; no signature or object changes. |
| Sheaf.Paper.SectionCoordinateOrientationSquare | E9 | Reuses the extracted standard case without an import cycle. |
| Sheaf.Paper.StandardAffineSectionOrientation | new, E9 | Owns the unchanged standard assertion and its proved fixed-presentation consequence. |

The downstream.py --uses search finds no external textual use of
sectionCoordinateCounit_standard. All dependent public mathematical statements retain
exactly their meanings. No target definition or statement changes, and no forced
adaptations of modules held by another group are made.

## Status

landed 20261027T021319-L-2756451 2026-10-27 (merge of deliver/E9/Sheaf.Paper.SectionCoordinateOrientationSquare)
