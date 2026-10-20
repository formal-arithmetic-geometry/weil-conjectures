# AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_finite_etale_model

## Reason

The assigned rework row still records the retired structural-flatness identifier.
The current item already contains E2's zero-hole restoration and its private
small-colimit flatness helper. Replace the duplicated small-cocone proof with
an application of the existing affine-chart ind-etale theorem to the identity
chart, then apply flatness of a filtered colimit of flat modules. This is an
actual proof simplification of the current source, not a rebase or a restoration
claim. It reuses the same short argument as the repaired purity-data module.

The old helper elaborates in the full file, but changing its final `exact h`
to `simpa only [Category.assoc] using h` exposes a conversion failure between
the representative cone and the selected coordinate-ring colimit. The new
proof works through the already proved chart interface, avoiding that explicit
conversion and the repeated construction of the stage natural transformation.

## Old

The private helper from the current source, verbatim:

```lean
private theorem finiteEtaleModel_small_strictHenselization_flat
    (R : CommRingCat.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    RingHom.Flat b.hom := by
  classical
  have := (strictHenselization_properties barY).2.1
  let I := SmallModel.{u} (strictHenselizationNeighbourhoods barY)
  let F := (equivSmallModel.{u} (strictHenselizationNeighbourhoods barY)).inverse
  let ψ (i : I) := ((AffineEtale.Spec (Spec R)).obj (F.obj i).1).hom
  let t : (Functor.const Iᵒᵖ).obj R ⟶ strictHenselizationAffineDiagram barY :=
    { app := fun i ↦ (ΓSpecIso R).inv ≫ (ψ i.unop).appTop
      naturality := fun i j a ↦ by
        dsimp only [Functor.const_obj_map, Functor.const_obj_obj]
        rw [Category.id_comp]
        symm
        change ((ΓSpecIso R).inv ≫ (ψ i.unop).appTop) ≫
          (Spec.map (F.map a.unop).1.left.unop).appTop =
            (ΓSpecIso R).inv ≫ (ψ j.unop).appTop
        rw [Category.assoc, ← Scheme.Hom.comp_appTop]
        exact congrArg (fun k ↦ (ΓSpecIso R).inv ≫ k.appTop) (F.map a.unop).1.w }
  apply RingHom.Flat.of_isColimit b Iᵒᵖ (strictHenselizationAffineDiagram barY)
    (t := t) (c := (colimit.cocone (strictHenselizationAffineDiagram barY)).ι)
    (colimit.isColimit (strictHenselizationAffineDiagram barY))
  intro i
  constructor
  · have : Etale (ψ i.unop) := inferInstance
    have : IsAffine ((AffineEtale.Spec (Spec R)).obj (F.obj i.unop).1).left := by
      change IsAffine (Spec (F.obj i.unop).1.left.unop)
      infer_instance
    exact (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (ΓSpecIso R).inv)).comp
        (Scheme.Hom.flat_appTop (f := ψ i.unop)
          (X := Spec (F.obj i.unop).1.left.unop) (Y := Spec R))
  · have h := strictHenselizationStructuralMap_eq barY i.unop
    apply Spec.map_injective
    rw [hb]
    change Spec.map ((ΓSpecIso R).inv ≫ (ψ i.unop).appTop ≫
      colimit.ι (strictHenselizationAffineDiagram barY) i) = _
    have ht : (ΓSpecIso R).inv ≫ (ψ i.unop).appTop =
        Spec.preimage (ψ i.unop) ≫ (ΓSpecIso (F.obj i.unop).1.left.unop).inv := by
      rw [ΓSpecIso_inv_naturality, Spec.map_preimage]
    rw [← Category.assoc, ht, Category.assoc, Spec.map_comp, Spec.map_comp,
      Spec.map_preimage]
    exact h
```

## New

The same private signature with the shorter proof:

```lean
private theorem finiteEtaleModel_small_strictHenselization_flat
    (R : CommRingCat.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    RingHom.Flat b.hom := by
  let : Algebra R (strictHenselizationRing barY) := b.hom.toAlgebra
  have he : Algebra.IndEtale R (strictHenselizationRing barY) :=
    strictHenselization_indEtale_of_affine_chart
      (A := strictHenselizationRing barY) barY R (𝟙 _)
      ⟨barY (IsLocalRing.closedPoint Ω), rfl⟩ (Iso.refl _) b.hom
      (by
        change Spec.map b ≫ 𝟙 _ = 𝟙 _ ≫ strictHenselizationStructuralMap barY
        simpa only [Category.comp_id, Category.id_comp] using hb)
  obtain ⟨J, _, _, P, hP⟩ := he.exists_colimitPresentation
  exact ModuleCat.flat_of_colimitPresentation
    (P.map (forget₂ _ (AlgCat R) ⋙ forget₂ _ (ModuleCat R))) fun j ↦ by
      change Module.Flat R (P.diag.obj j)
      have := hP j
      infer_instance
```

Add the private proof import
Sheaf.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale. Retain
WeilConjectures.RingTheory.ProEtale.FaithfullyFlat for the module-colimit
flatness theorem. Existing public imports, signatures, and definition bodies
are unchanged. The main finite-etale construction and its two branches are
unchanged. No data are chosen in definitions and no source-library file changes.

The complete module compiles in 5.9 seconds. A scratch copy prints only propext,
Classical.choice and Quot.sound for both the private helper and the public
theorem. A separate importing probe reuses the quarantined original signature
verbatim and the existing consumer call; both compile. There are zero holes
before and after, no split-off result, and no target meaning change.

The item's proof, proof_deps and proof_origin are updated to cite the actual
chart and module-colimit arguments. Its Lean attachment, mathematical statement,
incoming dependencies and blueprint unit route are preserved.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel | A9 | Only its private helper proof and a private proof import change. |
| Sheaf.AlgebraicGeometry.Morphisms.RegularDivisorStrictHenselRootSection | unclaimed; quarantined | Its original call has the identical signature and argument order; the importing consumer probe compiles. No adaptation. |

The private helper has no external users. tools/downstream.py finds no active
importer; searching quarantine finds the consumer listed above. No archive is
withdrawn, and no forced adaptation is needed.

## Status

landed 20261020T211627-L-3480368 2026-10-20 (merge of deliver/A9/Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel)
