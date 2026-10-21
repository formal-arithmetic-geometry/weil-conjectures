# AlgebraicGeometry.Etale.nonempty_addEquiv_sheafFiber_rightDerived_lowerStar_of_isAlgClosure

## Reason

Repair the returned delivery against the current restored source instead of
recreating a file from the obsolete quarantine base. Reapply the direct upstream
strict-localization argument while preserving the independent comparison repairs
and the current private compatibility API.

## Old

The current public signature, preserved verbatim:

```lean
theorem nonempty_addEquiv_sheafFiber_rightDerived_lowerStar_of_isAlgClosure
    {K : Type u} [Field K] (L : Type u) [Field L] [Algebra K L]
    [IsAlgClosure K L] [IsAlgClosed L] {X : Scheme.{u}} (a : X ⟶ Spec (.of K))
    [LocallyOfFiniteType a] [QuasiCompact a]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion)
    (q : ℕ) :
    Nonempty
      ((((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K L)))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj
          (((lowerStar AddCommGrpCat.{u + 1} a).rightDerived q).obj F)) ≃+
        Sheaf.H ((upperStar AddCommGrpCat.{u + 1}
          (pullback.fst a (Spec.map (CommRingCat.ofHom (algebraMap K L))))).obj F) q)
```

The current proof uses `strictHenselizationStructuralMap`, composes evaluation
with Spec of the small colimit comparison, and applies the small-model helper
`nonempty_addEquiv_strictLocalization`.

## New

The public signature is identical:

```lean
theorem nonempty_addEquiv_sheafFiber_rightDerived_lowerStar_of_isAlgClosure
    {K : Type u} [Field K] (L : Type u) [Field L] [Algebra K L]
    [IsAlgClosure K L] [IsAlgClosed L] {X : Scheme.{u}} (a : X ⟶ Spec (.of K))
    [LocallyOfFiniteType a] [QuasiCompact a]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (hF : F.IsTorsion)
    (q : ℕ) :
    Nonempty
      ((((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom (algebraMap K L)))).sheafFiber
          (A := AddCommGrpCat.{u + 1})).obj
          (((lowerStar AddCommGrpCat.{u + 1} a).rightDerived q).obj F)) ≃+
        Sheaf.H ((upperStar AddCommGrpCat.{u + 1}
          (pullback.fst a (Spec.map (CommRingCat.ofHom (algebraMap K L))))).obj F) q)
```

The proof uses `strictLocalizationToBase`, evaluation itself and its upstream
compatibility equation, and the existing `_toBase` helper. It then composes
cohomological topological invariance with pullback composition. Every current
import, all four private helper statements and proofs, and the public docstring
are retained exactly. No definition or consumer changes.

## Users

`tools/downstream.py` reports these nine downstream modules. All consumers retain
identical interfaces, including private helpers used by `import all`.

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.AffineDirectImageSupportBound` | unclaimed | Signatures, imports and private helpers unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.AffineSupportVanishing` | unclaimed | Signatures, imports and private helpers unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.Sites.AffineInfinityBoundarySupport` | unclaimed | Signatures, imports and private helpers unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.Sites.AffinePolynomialHigherProjectionSupport` | unclaimed | Signatures, imports and private helpers unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.Sites.AffinePolynomialInductionStep` | unclaimed | Signatures, imports and private helpers unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.Sites.AffinePolynomialProjectionSupport` | unclaimed | Signatures, imports and private helpers unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionBound` | unclaimed | Signatures, imports and private helpers unchanged; no adaptation. |
| `Sheaf.AlgebraicGeometry.Sites.AffineTorsionCohomologicalDimensionOfAffine` | unclaimed | Signatures, imports and private helpers unchanged; no adaptation. |
| `Sheaf.Paper.FiniteAffineDirectImageSupportBound` | unclaimed | Signatures, imports and private helpers unchanged; no adaptation. |

The quarantine archive is preserved; this delivery changes the active item file
only, its DAG proof/provenance and these repair records.

## Status

landed 20261021T203634-L-3847323 2026-10-21 (merge of deliver/K1/Sheaf.AlgebraicGeometry.Sites.FieldHigherDirectImageStalk)
