# AlgebraicGeometry.Scheme.PerfectProjection.Resolution.total and totalInverse

## Reason

Reuse the existing native signed-resolution chain maps. The previous forward map
is the same tensorAdjunctionTotal, and the previous inverse wrapper is inv of that
map using finite-total invertibility. SignedProjectionResolution.totalMate and
totalInverse use the identical constructions, with the already proved native unit
normalization. Unit comparisons appear only as arguments to a proof of invertibility;
proof irrelevance identifies the resulting inverse. Thus both maps retain their
source, target, summand formula, differential signs and mathematical values.
This avoids rebuilding the generic finite-total specialization inside conversions.
The signed module is public because public definitions use its public constructors.
No arbitrary data witness or postponed proof is introduced.

## Old

```lean
def Resolution.total :=
  letI := SheafOfModules.monoidalCategory (ring d Y)
  letI := SheafOfModules.monoidalCategory (ring d X)
  tensorAdjunctionTotal (ordinaryPull d f) (ordinaryPush d f)
    (proEtaleRingModuleAdjunction f (ring d Y) (ring d X) (coefficients d f))
    (proEtaleOrdinaryTensorPullback f (ring d Y) (ring d X) (coefficients d f))
    (fun {_ _ _ _} v z ↦ proEtaleOrdinaryTensorPullback_naturality
      f (ring d Y) (ring d X) (coefficients d f) _ _ _ _ v z) r.injective r.coefficient

def Resolution.totalInverse :=
  letI := SheafOfModules.monoidalCategory (ring d Y)
  letI := SheafOfModules.monoidalCategory (ring d X)
  tensorAdjunctionTotalInverse (ordinaryPull d f) (ordinaryPush d f)
    (proEtaleRingModuleAdjunction f (ring d Y) (ring d X) (coefficients d f))
    (proEtaleOrdinaryTensorPullback f (ring d Y) (ring d X) (coefficients d f))
    (fun {_ _ _ _} v z ↦ proEtaleOrdinaryTensorPullback_naturality
      f (ring d Y) (ring d X) (coefficients d f) _ _ _ _ v z)
    (ordinaryUnit d f) (fun M ↦ by
      have h := ordinaryUnit_coherence d f M
      rw [ordinaryRightUnit_eq, ordinaryRightUnit_eq] at h
      exact h)
    r.injective r.coefficient r.bounded r.package.N r.package.i r.package.p r.package.splitting
```

## New

```lean
def Resolution.total :=
  SignedProjectionResolution.totalMate f (ring d Y) (ring d X) (coefficients d f)
    r.injective r.coefficient

def Resolution.totalInverse :=
  SignedProjectionResolution.totalInverse f (ring d Y) (ring d X) (coefficients d f)
    r.injective r.coefficient r.package r.bounded
```

## Users

The downstream --uses Resolution.totalInverse search finds only the item. The
Resolution.total search additionally finds the ten short-name matches below;
all were read and refer to unrelated total constructions or prose.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PerfectProjectionFormula | U5 | Same signed maps; reuse both identities of the existing normalization theorem. |
| Sheaf.AlgebraicGeometry.SfFiniteEtaleProjectionFormula | unclaimed | Unrelated total name. |
| Sheaf.CategoryTheory.CondensedEquivariantBarData | unclaimed | Unrelated total name. |
| Sheaf.CategoryTheory.CondensedNormalSubgroupComparison | unclaimed | Unrelated total name. |
| Sheaf.CategoryTheory.CondensedProductBarComparison | unclaimed | Unrelated total name. |
| Sheaf.CategoryTheory.CyclicTotalTriangulated | unclaimed | Unrelated total name. |
| Sheaf.CategoryTheory.LatticeKoszulTriangulatedCupComparison | unclaimed | Unrelated total name. |
| Sheaf.Paper.KummerBarResolution | unclaimed | Unrelated total name. |
| Sheaf.Paper.ProjectionCoefficientTensorTotal | unclaimed | Unrelated total name. |
| Sheaf.SixFunctors.OpenTensorQuotientAugmentation | unclaimed | Unrelated total name. |
| WeilConjectures.SixFunctors.ProEtale.Adic.TwistedSection | unclaimed | Unrelated total name. |

No external declaration uses these maps; no forced adaptation is required.
No target changes statement or meaning.

## Status

landed 20261024T191427-L-349376 2026-10-24 (merge of deliver/U5/Sheaf.Paper.PerfectProjectionFormula)
