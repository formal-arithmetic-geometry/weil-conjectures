# WeilConjectures.PurityFiniteSetting.schemeGeometricFrobenius_naturality

## Reason

Complete the existing theorem while keeping chosen scheme pullbacks, constant
sheaves and derived localization folded. Local transparency attributes affect
only elaboration in this file. Generic private interfaces project composition
isos and trivializations to their nested object types, and give extensionality
for transformations between composite functors. Their proofs are categorical
identities in arbitrary categories; every helper is proved or explicitly
constructed. There is no new assumption or postponed proof.

The existing public definitions keep their data and meanings. Four abbreviation
keywords and four factorization rewrites are recorded in
`E8-frobenius-fiber-transparency.md`; the uniform characteristic proof is recorded
in `E8-frobenius-characteristic-api.md`; the public selected-data wrappers and
finite-ring proof are recorded in `E8-frobenius-selected-comparison-api.md`.

The new coherence module is a public import because its standard category
abbreviation occurs in the category data of the public definitions. Its only
mathematical theorem is the proved section-normalized composition coherence
result. The finite-coefficient import is now private: it is used only in the
proof of the new public `coefficient_ring_finite` theorem. The five obsolete
private imports are listed in report.md. No source-library module is changed.

This record is delivered at
`coord/changes/E8-scheme-geometric-frobenius-proof-scopes.md`. The landing
tool's reviewer-fix alias for that path is
`E8-scheme-geometric-frobenius-proof-scopes.change.md`. The return at
`23dd5937b` used the ordinary `.md` basename as a reviewer-fix alias, which
`tools/batch_land.py` does not accept. The record is included directly in this
packet; the proof and definition repairs above require no separate fix overlay.

## Old

```lean
theorem schemeGeometricFrobenius_naturality (P : PurityFiniteSetting.{u})
    (X₀ Y₀ : Over (Spec (CommRingCat.of P.field.k₀))) (f₀ : X₀ ⟶ Y₀) (d : ℕ)
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] [IsSeparated f₀.left]
    [SmoothOfRelativeDimension d (P.frobeniusMap f₀)] :
    Functor.whiskerRight (P.schemeGeometricFrobeniusComparison Y₀).hom
        (proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap f₀)) ≫
      (P.frobeniusGaloisSquareComparison X₀ Y₀ f₀ d).hom =
    (P.frobeniusSchemeSquareComparison X₀ Y₀ f₀ d).hom ≫
      Functor.whiskerLeft (proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap f₀))
        (P.schemeGeometricFrobeniusComparison X₀).hom := by
  sorry
```

## New

```lean
theorem schemeGeometricFrobenius_naturality (P : PurityFiniteSetting.{u})
    (X₀ Y₀ : Over (Spec (CommRingCat.of P.field.k₀))) (f₀ : X₀ ⟶ Y₀) (d : ℕ)
    [LocallyOfFiniteType f₀.left] [QuasiCompact f₀.left] [IsSeparated f₀.left]
    [SmoothOfRelativeDimension d (P.frobeniusMap f₀)] :
    Functor.whiskerRight (P.schemeGeometricFrobeniusComparison Y₀).hom
        (proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap f₀)) ≫
      (P.frobeniusGaloisSquareComparison X₀ Y₀ f₀ d).hom =
    (P.frobeniusSchemeSquareComparison X₀ Y₀ f₀ d).hom ≫
      Functor.whiskerLeft (proEtaleConstantRingDerivedPullback P.Ring (P.frobeniusMap f₀))
        (P.schemeGeometricFrobeniusComparison X₀).hom := by
  let : Finite P.Ring := coefficient_ring_finite P
  unfold schemeGeometricFrobeniusComparison frobeniusGaloisSquareComparison
    frobeniusSchemeSquareComparison frobeniusDerivedComposition
    frobeniusAbsoluteTrivialization frobeniusAbsoluteMap
  exact selected_derived_naturality P.field.p P.field.prime P.Ring
    (P.frobeniusFiber X₀).left (P.frobeniusFiber Y₀).left
    (P.frobeniusFiber_characteristic X₀) (P.frobeniusFiber_characteristic Y₀)
    (P.frobeniusMap f₀) P.field.a
    (P.frobeniusGaloisMap X₀) (P.frobeniusSchemeMap X₀)
    (P.frobeniusGaloisMap Y₀) (P.frobeniusSchemeMap Y₀)
    (P.schemeGeometricFrobenius_squares X₀ Y₀ f₀ d).2.2.2.1
    (P.schemeGeometricFrobenius_factorization X₀).2.2
    (P.schemeGeometricFrobenius_factorization Y₀).2.2
    (P.schemeGeometricFrobenius_squares X₀ Y₀ f₀ d).2.2.2.2.1
```

Local irreducibility keeps the existing ring aliases, scheme maps, ordinary
module functors and derived localization constructions folded. Selected
comparisons are exposed locally only when comparing with the source theorem.
No reducibility attribute is exported. No heartbeat or file-time limit changes,
metaprogramming diagnostic, kernel-check bypass, or additional hole is retained.

## Users

`tools/downstream.py Sheaf.SixFunctors.SchemeGeometricFrobenius --uses
frobeniusOrdinaryComposition frobeniusDerivedComposition
frobeniusAbsoluteTrivialization schemeGeometricFrobeniusComparison
schemeGeometricFrobenius_naturality` finds no current downstream Lean module.
The DAG parents and unit route are retained. Every existing statement and the
specified comparisons retain their meanings; no external adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.SchemeGeometricFrobenius | E8 | Completes naturality using the same selected data. |

The return at head `81167d8491` named six missing users of the proposed global
transparency change. That global change is omitted from this repaired packet:
`proEtaleConstantRingDerivedPullback` remains the original abbreviation, and
local irreducibility is applied only to `Functor.mapDerivedCategory` in the item.
Thus the following six users keep their existing code and meanings verbatim.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AbsoluteFrobeniusCoefficientNaturality | unclaimed | No change: the global functor remains the original abbreviation. |
| Sheaf.AlgebraicGeometry.ClassicalProEtaleProperBaseChange | unclaimed | No change: the global functor remains the original abbreviation. |
| Sheaf.AlgebraicGeometry.EtaleLocalShiftPartition | unclaimed | No change: the global functor remains the original abbreviation. |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | No change: the global functor remains the original abbreviation. |
| Sheaf.Paper.IntegralPullbackComposition | unclaimed | No change: the global functor remains the original abbreviation. |
| Sheaf.Paper.IntegralPullbackSystemComparison | unclaimed | No change: the global functor remains the original abbreviation. |

## Status

landed 20261021T120348-L-3836512 2026-10-21 (merge of deliver/E8/Sheaf.SixFunctors.SchemeGeometricFrobenius)
