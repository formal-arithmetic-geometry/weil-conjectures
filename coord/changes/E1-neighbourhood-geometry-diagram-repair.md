# AlgebraicGeometry.Etale.StrictLocalNeighbourhoodGeometry.smallModelFirst

## Reason

Restore the quarantined module assigned by coord/rework.tsv. The current upstream sync
removed the old `AlgebraicGeometry.Scheme.smallStrictHenselizationDiagram` name. The
canonical comparison now explicitly uses `Scheme.strictHenselizationDiagram`, as does
its proved inverse-coprojection formula in StrictHenselizationClosedFiberComparison.
The archived proof fails on the old name at line 93. Replace its four occurrences in
the proof with the current full affine diagram. This is a proof repair only: every
signature, definition body, attribute and public import remains identical to the archive.
The restored module compiles in 7.2 seconds through lcompile.py.

## Old

Archived at quarantine/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/NeighbourhoodGeometry.lean:

```lean
theorem smallModelFirst {X S : Scheme.{v}} {f : X ⟶ S}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] {s : Spec (.of Ω) ⟶ S}
    (Q : StrictLocalNeighbourhoodGeometry f s)
    (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    Q.smallModelLegs.app i ≫ pullback.fst ((strictLocalNeighbourhoods s).obj i).hom f =
      pullback.snd f (Scheme.strictHenselizationStructuralMap s) ≫
        (Scheme.strictHenselizationCone s).π.app (op (op i)) ≫
          Spec.map (Scheme.ΓSpecIso
            ((equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
              i).1.left.unop).inv := by
  classical
  let : HasColimit (AlgebraicGeometry.Scheme.smallStrictHenselizationDiagram s) := inferInstance
  let rep := (equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse
  let incl := Scheme.strictHenselizationAffineInclusion s
  let : incl.IsEquivalence := Scheme.strictHenselizationAffineInclusion_isEquivalence s
  have h := Functor.Final.ι_colimitIso_inv (rep ⋙ incl).op
    (AlgebraicGeometry.Scheme.smallStrictHenselizationDiagram s) (op i)
  change colimit.ι (AlgebraicGeometry.Scheme.smallStrictHenselizationDiagram s)
      (op (incl.obj (rep.obj i))) ≫
    (Scheme.smallStrictHenselizationColimitIso s).inv =
      colimit.ι (Scheme.strictHenselizationAffineDiagram s) (op i) at h
  have hh := congrArg Spec.map h
  simp only [Spec.map_comp] at hh
  change (strictLocalSmallModelPullbackIso f s).hom ≫ Q.legs.app i ≫ _ = _
  rw [Q.first]
  simp only [strictLocalSmallModelPullbackIso, asIso_hom, pullback.map,
    Category.assoc, pullback.lift_snd_assoc]
  change pullback.snd f (Scheme.strictHenselizationStructuralMap s) ≫
    Spec.map (Scheme.smallStrictHenselizationColimitIso s).inv ≫
      Spec.map (colimit.ι (AlgebraicGeometry.Scheme.smallStrictHenselizationDiagram s)
        (op (incl.obj (rep.obj i)))) ≫ _ = _
  simpa [Category.assoc, Scheme.strictHenselizationCone] using congrArg
    (fun k ↦ pullback.snd f (Scheme.strictHenselizationStructuralMap s) ≫ k ≫
      Spec.map (Scheme.ΓSpecIso (rep.obj i).1.left.unop).inv) hh

```

## New

Restored to lean/Sheaf/AlgebraicGeometry/StrictLocalSmallModel/NeighbourhoodGeometry.lean:

```lean
theorem smallModelFirst {X S : Scheme.{v}} {f : X ⟶ S}
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] {s : Spec (.of Ω) ⟶ S}
    (Q : StrictLocalNeighbourhoodGeometry f s)
    (i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)) :
    Q.smallModelLegs.app i ≫ pullback.fst ((strictLocalNeighbourhoods s).obj i).hom f =
      pullback.snd f (Scheme.strictHenselizationStructuralMap s) ≫
        (Scheme.strictHenselizationCone s).π.app (op (op i)) ≫
          Spec.map (Scheme.ΓSpecIso
            ((equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj
              i).1.left.unop).inv := by
  classical
  let : HasColimit (AlgebraicGeometry.Scheme.strictHenselizationDiagram s) := inferInstance
  let rep := (equivSmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)).inverse
  let incl := Scheme.strictHenselizationAffineInclusion s
  let : incl.IsEquivalence := Scheme.strictHenselizationAffineInclusion_isEquivalence s
  have h := Functor.Final.ι_colimitIso_inv (rep ⋙ incl).op
    (AlgebraicGeometry.Scheme.strictHenselizationDiagram s) (op i)
  change colimit.ι (AlgebraicGeometry.Scheme.strictHenselizationDiagram s)
      (op (incl.obj (rep.obj i))) ≫
    (Scheme.smallStrictHenselizationColimitIso s).inv =
      colimit.ι (Scheme.strictHenselizationAffineDiagram s) (op i) at h
  have hh := congrArg Spec.map h
  simp only [Spec.map_comp] at hh
  change (strictLocalSmallModelPullbackIso f s).hom ≫ Q.legs.app i ≫ _ = _
  rw [Q.first]
  simp only [strictLocalSmallModelPullbackIso, asIso_hom, pullback.map,
    Category.assoc, pullback.lift_snd_assoc]
  change pullback.snd f (Scheme.strictHenselizationStructuralMap s) ≫
    Spec.map (Scheme.smallStrictHenselizationColimitIso s).inv ≫
      Spec.map (colimit.ι (AlgebraicGeometry.Scheme.strictHenselizationDiagram s)
        (op (incl.obj (rep.obj i)))) ≫ _ = _
  simpa [Category.assoc, Scheme.strictHenselizationCone] using congrArg
    (fun k ↦ pullback.snd f (Scheme.strictHenselizationStructuralMap s) ≫ k ≫
      Spec.map (Scheme.ΓSpecIso (rep.obj i).1.left.unop).inv) hh

```

## Users

The live downstream.py census reports the item as unknown because it is quarantined.
A source import census of lean/Sheaf and quarantine/Sheaf gives these direct consumers.
No consumer adaptation is necessary: all declarations have their archived types and
all three definitions retain their archived bodies. In particular the pullback models,
cone, first-component equation and projection to X are the same. No target meaning
changes. Quarantined dependents remain their own restoration items.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.EtaleInjectiveSectionsComparison | not adapted | Identical restored API; quarantine source unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.MateContinuityPresentation | not adapted | Identical restored API; quarantine source unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.MateProjectionData | not adapted | Identical restored API; quarantine source unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalComplexSectionsMate | not adapted | Identical restored API; quarantine source unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceDerivedRestriction | not adapted | Identical restored API; quarantine source unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceRestriction | not adapted | Identical restored API; quarantine source unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalInjectiveSourceSections | not adapted | Identical restored API; quarantine source unchanged. |
| Sheaf.AlgebraicGeometry.StrictLocalSmallModel.StrictLocalUnderivedSectionsMate | not adapted | Identical restored API; quarantine source unchanged. |

## Status

landed 20261024T184930-L-3273415 2026-10-24 (merge of deliver/E1/Sheaf.AlgebraicGeometry.StrictLocalSmallModel.NeighbourhoodGeometry)
