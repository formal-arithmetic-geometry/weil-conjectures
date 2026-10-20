# AlgebraicGeometry.Scheme.GaloisCover.strict_hensel_root_purity_data

## Reason

The rework row still describes the retired structural-flatness call, but the
current source already contains R2's successful zero-hole restoration. Its
private flatness helper duplicates a construction of the pointed-neighbourhood
cocone. Replace that proof with the already proved identity-chart ind-etale
specialization and flatness of its filtered module colimit. This is a proof
change, not another restoration or a new definition repair.

The original rework error was an unknown
strictHenselization_structural_ringHom_flat. That retired declaration is not
reintroduced. The small-ring interface continues to be used throughout.

## Old

The private helper, verbatim from the current source:

```lean
private theorem purityData_small_strictHenselization_flat
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
private theorem purityData_small_strictHenselization_flat
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
WeilConjectures.RingTheory.ProEtale.FaithfullyFlat for
ModuleCat.flat_of_colimitPresentation. All public signatures, public imports,
and definition bodies remain verbatim. The explicit root quotient and divisor
construction and the tame-normalization assembly also remain verbatim.

The private helper and the public theorem both compile and print exactly
propext, Classical.choice and Quot.sound. No sorry is closed, introduced or
split off. No source-library module is edited. No target meaning changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootFiniteEtaleModel | E2; quarantined | Its archived call at line 151 uses the unchanged public signature. No adaptation is needed; the archive and all dependency edges remain intact. |

The helper is private, so it has no external users. The public theorem's
signature is unchanged. There are no forced adaptations.

## Status

landed 20261020T174743-L-790943 2026-10-20 (merge of deliver/E1/Sheaf.AlgebraicGeometry.Morphisms.StrictHenselRootPurityData)
