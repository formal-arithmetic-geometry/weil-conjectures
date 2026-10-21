# cbcCompletedOpenFiniteEtaleOrigins

## Reason

Close the original proof hole using finite-coordinate adjunctions and etale origin
transport. Preflight conservatively reports the added `section`, `variable`, `open`,
local-instance registration, and proof-elaboration options as an interface change.
All added declarations are private and all three instance registrations are local
to the existing namespace. Public imports, the public theorem signature, and every
public definition remain unchanged. The local coefficient-equivalence section is
closed before the theorem. No statement or definition repair is proposed.

## Old

```lean
theorem cbcCompletedOpenFiniteEtaleOrigins
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    (K : d.derived U)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness U (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction U n).obj K)) :
    Nonempty (∀ n : ℕ, FiniteEtaleOriginWitness T (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction T n).obj ((cbcDerivedOpenShriek d j inferInstance).obj K)))
```

The old proof was `by sorry`. The file opened `CategoryTheory` and had no proof helpers.

## New

```lean
theorem cbcCompletedOpenFiniteEtaleOrigins
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    (K : d.derived U)
    (W : ∀ n : ℕ, FiniteEtaleOriginWitness U (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction U n).obj K)) :
    Nonempty (∀ n : ℕ, FiniteEtaleOriginWitness T (A ⧸ d.ideal ^ (n + 1))
      ((d.reduction T n).obj ((cbcDerivedOpenShriek d j inferInstance).obj K)))
```

The proof is complete. Added proved private helpers for exact adjunction localization,
restriction along a coefficient isomorphism, finite scalar-restriction exactness,
finite reduction adjunction, and reduction/open-extension comparison. The helpers use
`CategoryTheory.Limits` and `Opposite` locally to this file. Local instance registration
supplies additive and exactness properties only while elaborating this file. New imports
are proof-only, not public. These scope additions do not alter any imported signature.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CompletedOpenFiniteEtaleOrigins | C9 | Original theorem proved; signature unchanged. |
| Sheaf.Paper.CompleteCompactSupportProetale | B7 | Direct consumer of the theorem; original proof continues to use exactly the same signature; no adaptation. |
| Sheaf.Paper.CompleteProetaleStrictTowerRealization | not adapted | Transitive importer; no public interface change. |
| Sheaf.Paper.CompletedOpenStrictMateIdentification | not adapted | Transitive importer; no public interface change. |
| Sheaf.Paper.ExtensionZeroPerfectModelTransport | not adapted | Transitive importer; no public interface change. |
| Sheaf.Paper.ExtensionZeroStratifiedPerfect | not adapted | Transitive importer; no public interface change. |
| Sheaf.Paper.NormalizedCoefficientFamilies | not adapted | Transitive importer; no public interface change. |
| Sheaf.Paper.RationalPullbackCompositionCoherence | not adapted | Transitive importer; no public interface change. |
| Sheaf.Paper.RationalRealizationPullbackComparison | not adapted | Transitive importer; no public interface change. |
| Sheaf.Paper.RationalRealizationScalarCoherence | not adapted | Transitive importer; no public interface change. |
| Sheaf.SixFunctors.OpenExchangeRoosRestriction | not adapted | Transitive importer; no public interface change. |

`tools/downstream.py --uses cbcCompletedOpenFiniteEtaleOrigins` finds only the item
and `Sheaf.Paper.CompleteCompactSupportProetale` as textual users. No target meaning
changes and no consumer adaptations are necessary.

## Status

landed 20261021T170722-L-2753292 2026-10-21 (merge of deliver/C9/Sheaf.Paper.CompletedOpenFiniteEtaleOrigins)
