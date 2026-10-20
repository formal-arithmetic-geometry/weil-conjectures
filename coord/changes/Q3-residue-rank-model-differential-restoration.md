# AlgebraicGeometry.Scheme.residueRankModel_differential_eval_eq_zero

## Reason

Restore the assigned module from its current rework archive. The live Lean path is
absent after the cluster restore recorded in `coord/rework.tsv`; the archived proof
has zero holes. Its direct quarantined consumer `PicardH1CommonMinimalModel` and
its DAG parent still need the theorem. Its affine cohomology dependency is now
restored. This is restoration of the missing theorem, not withdrawal or a new split.

## Old

The live path `lean/Sheaf/AlgebraicGeometry/ResidueRankModelDifferential.lean` is
absent. Its preserved source is
`quarantine/Sheaf/AlgebraicGeometry/ResidueRankModelDifferential.lean`, whose public
signature is:

```lean
theorem residueRankModel_differential_eval_eq_zero
    [∀ Y : Scheme.{v},
      HasDerivedCategory.{v + 1} (SheafOfModules.{v} (moduleRings Y.toRingedSpace))]
    [∀ (Y : Scheme.{v}) (U : Y.Opens), HasDerivedCategory.{v + 1}
      (SheafOfModules.{v} ((moduleRings Y.toRingedSpace).over U))]
    (W : Scheme.{v}) (E : schemeDerivedCategory W) (w : W)
    (hfin : ∀ j : ℤ, Module.Finite (W.residueField w) (derivedFiberCohomology W E j w))
    (U : W.Opens) (hwU : w ∈ U) (hU : IsAffineOpen U)
    (K : CochainComplex (SheafOfModules.{v} ((moduleRings W.toRingedSpace).over U)) ℤ)
    (hb : ∃ a b : ℤ, ∀ j : ℤ, j < a ∨ b < j → IsZero (K.X j))
    (hrank : ∀ j : ℤ, Nonempty (K.X j ≅ SheafOfModules.free
      (R := (moduleRings W.toRingedSpace).over U)
      (ULift.{v} (Fin (derivedFiberBetti W E j w)))))
    (he : Nonempty ((SheafOfModules.overFunctor.{v}
      (moduleRings W.toRingedSpace) U).mapDerivedCategory.obj E ≅
        DerivedCategory.Q.obj K))
    (m : ℕ)
    (e1 : (K.X 1).val.obj (.op (Over.mk (𝟙 U))) ≃ₗ[Γ(W, U)] (Fin m → Γ(W, U)))
    (t : (K.X 0).val.obj (.op (Over.mk (𝟙 U)))) :
    ∀ i, W.evaluation U w hwU
      (e1 ((K.d 0 1).val.app (.op (Over.mk (𝟙 U))) t) i) = 0
```

## New

Restore the archived module verbatim, including the exact signature above, both
public imports, all proof imports, both private proved
helpers, and the complete public proof. There is no change to a definition,
statement, universe, visibility, or target. The proof uses all three existing DAG
proof dependencies. Its attachment and proof plan already describe this proof,
so no node field needs alteration.

The proof imports include the affine section-cohomology comparison, finite
vector-space lemmas, free-sheaf section coordinates, and finite scalar extension.
All are retained. No source-library file is changed.

## Users

The source-only `tools/downstream.py` check with `--allow-missing --uses
residueRankModel_differential_eval_eq_zero` finds zero live consumers. A separate
import-graph traversal including the quarantine archive finds these thirteen
consumers. The sole direct consumer is `PicardH1CommonMinimalModel`, whose call
supplies precisely the original hypotheses and a section in the degree-zero frame.
All other consumers are transitive. The restored interface is verbatim, so no
consumer requires adaptation; their quarantine restoration remains their own work.
The unchanged archived direct consumer was compiled against the restored sandbox
output: it fails at its imports, before theorem elaboration, because old
`Sheaf.AlgebraicGeometry.PerfectComplex` artifacts conflict with the adopted
`WeilConjectures.AlgebraicGeometry.PerfectComplex` definition of `IsPerfect`
(2.6 seconds). This unrelated stale dependency does not require a source adaptation.
The actual call was checked against the preserved signature. The maintainer performs
the independent delivery review.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.CubeFiberTrivialityOpen | quarantined; not adapted | Transitive consumer; original interface restored. |
| Sheaf.AlgebraicGeometry.GeneralTheoremOfCube | quarantined; not adapted | Transitive consumer; original interface restored. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentCyclePresentation | quarantined; not adapted | Transitive consumer; original interface restored. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentLocalModel | quarantined; not adapted | Transitive consumer; original interface restored. |
| Sheaf.AlgebraicGeometry.PicardH1BaseDescentSectionLifting | quarantined; not adapted | Transitive consumer; original interface restored. |
| Sheaf.AlgebraicGeometry.PicardH1CommonMinimalModel | quarantined; not adapted | Direct caller; original statement and public imports restored. |
| Sheaf.AlgebraicGeometry.PicardH1IntersectionSection | quarantined; not adapted | Transitive consumer; original interface restored. |
| Sheaf.AlgebraicGeometry.PicardH1LocalDescent | quarantined; not adapted | Transitive consumer; original interface restored. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescent | quarantined; not adapted | Transitive consumer; original interface restored. |
| Sheaf.AlgebraicGeometry.PicardH1LocalSectionBaseDescentGenerator | quarantined; not adapted | Transitive consumer; original interface restored. |
| Sheaf.AlgebraicGeometry.PicardH1MultipleLocus | quarantined; not adapted | Transitive consumer; original interface restored. |
| Sheaf.AlgebraicGeometry.PicardProductOpen | quarantined; not adapted | Transitive consumer; original interface restored. |
| Sheaf.AlgebraicGeometry.PicardProductOpenData | quarantined; not adapted | Transitive consumer; original interface restored. |

## Status

landed 20261020T235617-L-1195705 2026-10-20 (merge of deliver/Q3/Sheaf.AlgebraicGeometry.ResidueRankModelDifferential)
