# AlgebraicGeometry.Scheme.affineFree_residueSections_cohomologyLinearEquiv

## Reason

Restore the assigned module from the quarantine path in its current `coord/rework.tsv`
row. The archive contains a complete theorem with zero holes, while its live `lean/`
path is absent. The two archived direct consumers and their DAG proof dependencies
still require this statement. Its derived-model dependency has already been restored
by R1. This delivery restores the theorem, keeps its entire signature and public
imports, and simplifies the final complex comparison without changing its endpoints.
No definition or target statement changes.

## Old

The live module is absent. Its preserved source is
`quarantine/Sheaf/AlgebraicGeometry/AffineFreeResidueSectionsCohomology.lean`.
The archived theorem signature is:

```lean
theorem affineFree_residueSections_cohomologyLinearEquiv
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (w : W)
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (K : CochainComplex (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hb : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (K.X j))
    (r : ℤ → ℕ)
    (hrank : ∀ j : ℤ, Nonempty (K.X j ≅ SheafOfModules.free
      (R := (moduleRings W.toRingedSpace).over U)
      (ULift.{v} (Fin (r j)))))
    (he : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj K)) :
    let F : SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U) ⥤
      ModuleCat.{v} Γ(W, U) :=
      SheafOfModules.evaluation _
      (.op (Over.mk (𝟙 U)))
    letI : F.Additive := inferInstanceAs
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ _).Additive)
    let T := ModuleCat.extendScalars.{v, v, v} (W.evaluation U w hwU).hom
    letI : T.Additive := (ModuleCat.extendRestrictScalarsAdj _).left_adjoint_additive
    let C := ((F ⋙ T).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
    ∀ j : ℤ, Nonempty (derivedFiberCohomology W E j w ≃ₗ[W.residueField w]
      C.homology j)
```

The final complex comparison used:

```lean
    (Functor.mapHomologicalComplexCompIso (tilde.toTildeΓNatIso).symm (.up ℤ)).app C ≪≫
      (Functor.mapHomologicalComplexIdIso (ModuleCat.{v} (W.residueField w)) (.up ℤ)).app C
```

## New

Restore `lean/Sheaf/AlgebraicGeometry/AffineFreeResidueSectionsCohomology.lean`
with exactly the archived theorem signature above, the same public imports, and a
complete proof. The final comparison instead uses the natural isomorphism directly:

```lean
    (NatIso.mapHomologicalComplex tilde.toTildeΓNatIso.symm (.up ℤ)).app C ≪≫
      (Functor.mapHomologicalComplexIdIso (ModuleCat.{v} (W.residueField w)) (.up ℤ)).app C
```

Mapping functor composition to complexes agrees definitionally with composing the
induced functors. The direct natural-isomorphism component therefore has the same
endpoints and avoids the extra composition comparison. All support, free-module,
K-flatness, and homology arguments are retained. Rank zero and the zero complex use
the same equivalences; an empty open has no point satisfying `hwU`.

## Users

`tools/downstream.py` with `--allow-missing --uses
 affineFree_residueSections_cohomologyLinearEquiv` finds no current live importers.
A source import-graph traversal including quarantined modules finds the following
16 consumers, including the two direct consumers named below. Public imports and
the theorem signature are unchanged, so no adaptation is required. The independent
maintainer reader checks this restoration through the normal delivery review.
Both unchanged archived direct consumers compiled against the final sandbox theorem
(`AffineBettiModelResidueMinimality`: 22.4 seconds;
`ResidueRankModelDifferential`: 17.0 seconds).

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.AffineBettiModelResidueMinimality | quarantined; no adaptation | Direct caller; identical theorem signature and public imports. |
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | quarantined; no adaptation | Transitive caller; identical theorem signature and public imports. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | quarantined; no adaptation | Transitive caller; identical theorem signature and public imports. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | quarantined; no adaptation | Transitive caller; identical theorem signature and public imports. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | quarantined; no adaptation | Transitive caller; identical theorem signature and public imports. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | quarantined; no adaptation | Transitive caller; identical theorem signature and public imports. |
| Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel | quarantined; no adaptation | Transitive caller; identical theorem signature and public imports. |
| Sheaf.AlgebraicGeometry.PicardH1FixedModelComparison | quarantined; no adaptation | Transitive caller; identical theorem signature and public imports. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | quarantined; no adaptation | Transitive caller; identical theorem signature and public imports. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | quarantined; no adaptation | Transitive caller; identical theorem signature and public imports. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | quarantined; no adaptation | Transitive caller; identical theorem signature and public imports. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | quarantined; no adaptation | Transitive caller; identical theorem signature and public imports. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | quarantined; no adaptation | Transitive caller; identical theorem signature and public imports. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | quarantined; no adaptation | Transitive caller; identical theorem signature and public imports. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | quarantined; no adaptation | Transitive caller; identical theorem signature and public imports. |
| Sheaf.AlgebraicGeometry.ResidueRankModelDifferential | quarantined; no adaptation | Direct caller; identical theorem signature and public imports. |

## Status

landed 20261020T233048-L-887751 2026-10-20 (merge of deliver/A6/Sheaf.AlgebraicGeometry.AffineFreeResidueSectionsCohomology)
