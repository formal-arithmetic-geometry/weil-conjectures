# AlgebraicGeometry.Scheme.AdicCoefficientDatum.constructible_preservation

## Reason

The corollary uses `E : Type (u + 1)` and the unlifted datum
`pbcPadicCoefficientDatum l E`. The existing preservation theorem instead takes
`E : Type u` and uses `pbcIntegralDatum l E`, whose coefficient ring is a ULift.
They are not definitionally the same coefficient sheaf, derived category, reduction
unit or quotient action. The new lemma records the source proposition for the original
adic datum. It asserts only object preservation and is a strict geometric part of the
corollary, independent of its natural-isomorphism and triangulation assertions.

## Old

No declaration of this name. The existing `WeilConjectures.pbc_preservation_constructible`
and every existing public signature, definition and visibility remain unchanged.

## New

```lean
theorem AdicCoefficientDatum.constructible_preservation
    {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    [IsNoetherian X] [IsNoetherian Y] [IsNoetherian X'] [IsNoetherian Y']
    (hDimX : ∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))
    (hDimY : ∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))
    (hDimX' : ∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))
    (hDimY' : ∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))
    [IsProper f] [IsProper f']
    (N : ℕ) (hN : 0 < N) (hAnn : (N : A ⧸ d.ideal) = 0)
    (hNX : IsUnit (N : Γ(X, ⊤))) (hNY : IsUnit (N : Γ(Y, ⊤)))
    (hNX' : IsUnit (N : Γ(X', ⊤))) (hNY' : IsUnit (N : Γ(Y', ⊤)))
    (e : ℕ)
    (hFibres : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (y : Spec (.of Ω) ⟶ Y),
      topologicalKrullDim (pullback f y : Scheme.{u}) ≤ (e : WithBot ℕ∞))
    (K : d.derived X) (hK : PbcIsBoundedConstructibleComplete X d K) :
    PbcIsBoundedConstructibleComplete Y d ((d.push f).obj K) ∧
      PbcIsBoundedConstructibleComplete Y' d
        ((d.completedPull g).obj ((d.push f).obj K)) ∧
      PbcIsBoundedConstructibleComplete X' d ((d.completedPull g').obj K) ∧
      PbcIsBoundedConstructibleComplete Y' d
        ((d.push f').obj ((d.completedPull g').obj K))
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstructibleCompleteBaseChange | K1 | New proof-only import; applies the second and fourth object-preservation clauses. |

`Sheaf.Paper.CompletedConstructibleReductionControl` is also new, held by K1;
its sole consumer is `Sheaf.Paper.CompletedConstructiblePreservation`, which proves
the completeness and normalized assembly from its finite-level conclusion.
Its exact signature and predicate definition are in the new module, and its node
records the finite-level portion of the source proof. This adds an interface; it
changes no existing signature or definition.

The new modules had no previous consumers. No existing definition or signature changes,
so no forced adaptations or target-statement rechecks arise. The item's two existing
direct consumers, `Sheaf.Paper.FiniteExtensionProperBaseChange` and
`WeilConjectures.WeilSheaf.LowerShriekFunctoriality`, see the same public imports and
signatures. They do not mention the new declaration.

## Status

landed 20261020T051434-L-1681519 2026-10-20 (merge of deliver/K1/Sheaf.Paper.ConstructibleCompleteBaseChange)
