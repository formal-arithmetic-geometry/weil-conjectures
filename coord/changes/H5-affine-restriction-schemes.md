# AlgebraicGeometry.Scheme.Modules.affineRealizationRestriction

## Reason

The canonical restriction was elaborated through the comma-category chart projection.
Its adjunction and cohomology map therefore carry the inferred schemes
`((MorphismProperty.Over.pullback _ _ f).obj V).left`, while the public ordinary
cohomology group names `Limits.pullback V.hom f`. These schemes are definitionally
equal, but kernel conversion after specialization unfolds the large tensor and
cohomology constructions. In the H5 proof the restriction identification exceeded
30,000 kernel heartbeats, and the full original-interface check exceeded 120 seconds.

Name the same arrow `b.left` with its explicit fibre-product source and target.
Factor the existing formula into the new public construction
`tensorCompositeCohomologyRestriction`, parameterized by arbitrary schemes and coefficient
module. Its proved defining equation expands to exactly the original adjunct and
cohomology map. A proved named coefficient-object equality supplies the same transport
as the original `congrArg`; proof irrelevance identifies these equality proofs.
The new module marks this construction irreducible and exposes its defining equation,
so specialization does not repeatedly unfold the large coefficient sheaves.

There is no new choice, normalization, hypothesis, conclusion, or coefficient
identification. The chosen adjunction is the same existing chosen adjunction.
The old restriction signature, visibility and attributes remain verbatim, and all
old public imports remain. The definition module adds the public import
`Sheaf.AlgebraicGeometry.TensorCompositeCohomologyRestriction` for its new body.
The module is unclaimed in the current claim records.

## Old

```lean
def affineRealizationRestriction {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) (q : ℕ) {V V' : S.Etale} (h : V' ⟶ V) :
    AddCommGrpCat.of ((RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
      (affineRealizationCoefficient f G V)) ⟶
    AddCommGrpCat.of ((RingedSpace.moduleCohomology (Limits.pullback V'.hom f).toRingedSpace q).obj
      (affineRealizationCoefficient f G V')) := by
  let B : S.Etale ⥤ X.Etale :=
    MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f
  let b : B.obj V' ⟶ B.obj V := B.map h
  let adj : tensorPullback b.left ⊣ pushforward b.left :=
    Classical.choose (exists_tensorPullbackAdjunction b.left)
  let ψ : (tensorPullback b.left).obj (affineRealizationCoefficient f G V) ⟶
      affineRealizationCoefficient f G V' :=
    (tensorSectionsComp b.left (Limits.pullback.snd V.hom f)).hom.app G ≫
      eqToHom (congrArg (fun j ↦ (tensorPullback j).obj G) b.w)
  exact moduleCohomologyFMap b.left (adj.homEquiv _ _ ψ) q
```

## New

```lean
def affineRealizationRestriction {X S : Scheme.{u}} (f : X ⟶ S)
    (G : X.Modules) (q : ℕ) {V V' : S.Etale} (h : V' ⟶ V) :
    AddCommGrpCat.of ((RingedSpace.moduleCohomology (Limits.pullback V.hom f).toRingedSpace q).obj
      (affineRealizationCoefficient f G V)) ⟶
    AddCommGrpCat.of ((RingedSpace.moduleCohomology (Limits.pullback V'.hom f).toRingedSpace q).obj
      (affineRealizationCoefficient f G V')) := by
  let B : S.Etale ⥤ X.Etale :=
    MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ f
  let b : B.obj V' ⟶ B.obj V := B.map h
  -- Fix the underlying schemes before forming the adjunction and cohomology map.
  let a : Limits.pullback V'.hom f ⟶ Limits.pullback V.hom f := b.left
  exact tensorCompositeCohomologyRestriction a (pullback.snd V.hom f)
    (pullback.snd V'.hom f) b.w G q
```

## Users

The complete `tools/downstream.py ... --uses affineRealizationRestriction` list
has six modules, including its defining module. The statements still refer to
the same canonical restriction. No consumer statement becomes weaker, stronger,
or different. No edits in a module held by another group are included.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.AffineCohomologyComparisonData | unclaimed | Explicit arrow type and factored canonical formula; other definitions and theorems unchanged. |
| Sheaf.AlgebraicGeometry.AffineCohomologyEtaleModuleRealization | unclaimed | Chart naturality, evaluation and realization statements retain the same restriction. Its proofs use the public interface without unfolding this construction. |
| Sheaf.AlgebraicGeometry.AffineCohomologyRawRestriction | unclaimed | Both naturality equations retain the same canonical map; their existing proof compositions are unchanged. |
| Sheaf.AlgebraicGeometry.AffineComparisonPullback | A7 | Its comparison square uses the same adjunct and coefficient transport. Its statement is unchanged; no adaptation is included. |
| Sheaf.AlgebraicGeometry.UnitAffineComparisonTransport | unclaimed | The parent theorem applies the same canonical naturality theorem and retains its statement. |
| Sheaf.AlgebraicGeometry.UnitAffineComparisonTransportNaturality | H5 | Proves the assigned theorem from coefficient functoriality with explicit fibre-product schemes. |

The definition node `def-weil-pbc-affine-cohomology-comparison-data` retains its
statement and Lean attachment; its proof description records the typed, factored construction. The new node
`def-tensor-composite-cohomology-restriction` records the constructed map and its
proved formula; it contains no holes. The target statements and the unit route stay unchanged. The
independent delivery review should check that this refactoring preserves
the canonical construction, including any target meanings that depend on it.

## Status

landed 20261026T082110-L-2132403 2026-10-26 (merge of deliver/H5/Sheaf.AlgebraicGeometry.UnitAffineComparisonTransportNaturality)
