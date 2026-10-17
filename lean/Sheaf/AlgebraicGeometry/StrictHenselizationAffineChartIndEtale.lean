/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K2
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.RingTheory.ProEtale.IndEtale
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples

/-! # The strict henselization is ind-etale over an affine chart

Source: Stacks Project, Tag 04HX, proof, and Tags 04GW and 04GP.
(blueprint: lem-weil-pbc-strict-henselization-affine-chart-ind-etale).
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The ring of a strict henselization is ind-etale over any affine neighbourhood
of its geometric point, with the algebra structure specified by its structural map.
Source: Stacks Project, Tag 04HX, proof, using Tags 04GW and 04GP.
(blueprint: lem-weil-pbc-strict-henselization-affine-chart-ind-etale).

Proof: Factor the geometric point through the open immersion i. Restrict affine
pointed etale neighbourhoods to those whose structural map factors through i.
`etale_local_ring_triples` proves this restriction cofinal and identifies its
coordinate-ring diagram with the etale residue-triples diagram. The small model
in `strictHenselizationAffineDiagram` is equivalent to the affine pointed-neighbourhood
category by `strictHenselizationAffineInclusion_isEquivalence`. Compare its colimit
with the full affine diagram by the final-functor colimit isomorphism. Its coprojection
equation identifies the two structural maps, using the characterizing equation of
`exists_strictHenselizationStructuralMap` on any small representative.
Cofilteredness transfers to the chart subcategory and then filteredness transfers
through the equivalence with triples; take a small representative category of triples.
Regard each triple as an R-algebra via its structural map.
Every transition is R-linear. Cocone naturality and filteredness show that the
composites R → B → colim B agree for all triples B, defining the structural map ρ.
Cofinality identifies this colimit with strictHenselizationRing s. The equations defining
strictHenselizationStructuralMap identify the induced R-map with the map a after
transport through e. Indeed their spectra agree after composing with i, which is
mono, and full faithfulness of Spec then gives equality of ring maps. Transport
the ring colimit along this isomorphism to A. `RingHom.IndEtale.iff_exists` turns
the compatible filtered etale ring presentation into the required ind-etale algebra.

Edge cases: no local or reduced hypothesis on R is used. The chart containing
the specified geometric point is nonempty, and the pointed-neighbourhood category
has an object, so no empty filtered diagram is asserted. The identification e is
arbitrary; the equation ha fixes the transported R-algebra structure. -/
theorem strictHenselization_indEtale_of_affine_chart
    {S : Scheme.{u}} {Ω A : Type u} [Field Ω] [IsAlgClosed Ω] [CommRing A]
    (s : Spec (.of Ω) ⟶ S) (R : CommRingCat.{u})
    (i : Spec R ⟶ S) [IsOpenImmersion i]
    (hs : s (IsLocalRing.closedPoint Ω) ∈ Set.range i)
    (e : Spec (.of A) ≅ strictHenselizationScheme s)
    (a : R →+* A)
    (ha : Spec.map (CommRingCat.ofHom a) ≫ i =
      e.hom ≫ strictHenselizationStructuralMap s) :
    letI : Algebra R A := a.toAlgebra
    Algebra.IndEtale R A :=
  open CategoryTheory.Limits Opposite in
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  by
    classical
    -- The spectrum of a field has one point, so the point factors through the chart.
    have hrange : Set.range s ⊆ Set.range i := by
      rintro _ ⟨x, rfl⟩
      have hx : x = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
      simpa only [hx] using hs
    obtain ⟨xR, hxR⟩ : ∃ xR : Spec (.of Ω) ⟶ Spec R, xR ≫ i = s :=
      ⟨IsOpenImmersion.lift i s hrange, IsOpenImmersion.lift_fac i s hrange⟩
    subst s
    let s := xR ≫ i
    let p := (SpecToEquivOfField Ω (Spec R) xR).1
    let F := (Spec R).residueField p
    let ε := (SpecToEquivOfField Ω (Spec R) xR).2
    let : Algebra F Ω := ε.hom.toAlgebra
    let K := separableClosure F Ω
    let Nall := (pointSmallEtale s).fiber.Elements
    let P : ObjectProperty Nall := fun n ↦ IsAffine n.1.left
    let Q : ObjectProperty P.FullSubcategory := fun z ↦
      ∃ g : z.obj.1.left ⟶ Spec R, g ≫ i = z.obj.1.hom
    let D := (P.ι ⋙ CategoryOfElements.π (pointSmallEtale s).fiber ⋙
      Etale.forget S ⋙ Over.forget S).op ⋙ Scheme.Γ
    obtain ⟨hN, _, hshrink, _, E, δ, hδ, cn, _, c, ⟨hcn⟩, ⟨_⟩, ⟨hc⟩,
        _, t, _, ht⟩ := etale_local_ring_triples S Ω R i xR
    have : IsCofiltered P.FullSubcategory := hN
    have : IsCofiltered Q.FullSubcategory :=
      IsCofiltered.of_exists_of_isCofiltered_of_fullyFaithful Q.ι hshrink
    have : IsFiltered (EtaleResidueTriples R p K
        (CommRingCat.ofHom (algebraMap F K))) := IsFiltered.of_equivalence E
    let t₀ := Classical.choice (IsFiltered.nonempty (C := EtaleResidueTriples R p K
      (CommRingCat.ofHom (algebraMap F K))))
    let ρ := t₀.α ≫ c.ι.app t₀
    have hcompat {x y : EtaleResidueTriples R p K
        (CommRingCat.ofHom (algebraMap F K))} (f : x ⟶ y) :
        x.α ≫ c.ι.app x = y.α ≫ c.ι.app y := by
      have hw := congrArg Over.Hom.left (Under.w f.hom)
      change x.α ≫ (etaleResidueTriplesRingDiagram R p K
        (CommRingCat.ofHom (algebraMap F K))).map f = y.α at hw
      exact (congrArg (fun z ↦ x.α ≫ z) (c.w f)).symm.trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun z ↦ z ≫ c.ι.app y) hw))
    have hρ (x : EtaleResidueTriples R p K
        (CommRingCat.ofHom (algebraMap F K))) : x.α ≫ c.ι.app x = ρ :=
      (hcompat (IsFiltered.leftToMax x t₀)).trans
        (hcompat (IsFiltered.rightToMax x t₀)).symm
    let : HasColimit D := by
      change HasColimit (strictHenselizationDiagram s)
      infer_instance
    let incl := strictHenselizationAffineInclusion s
    let : incl.IsEquivalence := strictHenselizationAffineInclusion_isEquivalence s
    let rep := (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse
    let cmp₀ : strictHenselizationRing s ≅ colimit D :=
      Functor.Final.colimitIso (rep ⋙ incl).op D
    let cmp : strictHenselizationRing s ≅ cn.pt :=
      cmp₀ ≪≫ colimit.isoColimitCocone ⟨cn, hcn⟩
    have hbase : Spec.map cmp₀.inv ≫ strictLocalizationToBase s =
        strictHenselizationStructuralMap s := by
      have := (strictHenselization_properties s).2.1
      let j := Classical.choice (IsCofiltered.nonempty (C :=
        SmallModel.{u} (strictHenselizationNeighbourhoods s)))
      have hbig := strictLocalizationCone_π_app_hom s (incl.obj (rep.obj j))
      rw [strictLocalizationCone_π_app] at hbig
      have hsmall := (exists_strictHenselizationStructuralMap s).choose_spec j
      have hleg := Functor.Final.ι_colimitIso_inv (rep ⋙ incl).op D (op j)
      change colimit.ι D (op (incl.obj (rep.obj j))) ≫ cmp₀.inv =
        colimit.ι (strictHenselizationAffineDiagram s) (op j) at hleg
      let B := (rep.obj j).1.left.unop
      let f : Spec B ⟶ S := ((AffineEtale.Spec S).obj (rep.obj j).1).hom
      change (Spec.map (colimit.ι D (op (incl.obj (rep.obj j)))) ≫
        inv (Spec B).toSpecΓ) ≫ f = strictLocalizationToBase s at hbig
      change Spec.map (colimit.ι (strictHenselizationAffineDiagram s) (op j)) ≫
        Spec.map (ΓSpecIso B).inv ≫ f = strictHenselizationStructuralMap s at hsmall
      have hinv : inv (Spec B).toSpecΓ = Spec.map (ΓSpecIso B).inv := by
        apply (cancel_mono (Spec B).toSpecΓ).1
        simp only [IsIso.inv_hom_id, SpecMap_ΓSpecIso_inv_toSpecΓ]
      rw [hinv] at hbig
      have hh := congrArg (fun z ↦ Spec.map z ≫ Spec.map (ΓSpecIso B).inv ≫ f) hleg
      simp only [Spec.map_comp, Category.assoc] at hh
      rw [← hbig]
      simpa only [Category.assoc] using hh.trans hsmall
    let ringIso : strictHenselizationRing s ≅ c.pt := cmp ≪≫ t
    -- The chart object identifies the transported R-map with the structural map.
    have hstrmap : Spec.map (ρ ≫ ringIso.inv) ≫ i =
        strictHenselizationStructuralMap s := by
      let b : P.FullSubcategory :=
        ⟨(pointSmallEtale s).fiber.elementsMk (Etale.mk i) (Over.homMk xR rfl),
          inferInstanceAs (IsAffine (Spec R))⟩
      let d : Q.FullSubcategory := ⟨b, ⟨𝟙 _, Category.id_comp i⟩⟩
      have hcmp : colimit.ι D (op b) ≫ cmp₀.inv ≫ cmp.hom =
          cn.ι.app (op b) := by
        simp only [cmp, Iso.trans_hom, ← Category.assoc, Iso.inv_hom_id,
          Category.comp_id]
        exact colimit.isoColimitCocone_ι_hom ⟨cn, hcn⟩ (op b)
      have htrip := (hδ d).1 (𝟙 _) (Category.id_comp i)
      change (ΓSpecIso R).inv ≫ δ.hom.app (op d) =
        (E.functor.obj (op d)).α at htrip
      have hρchart : (ΓSpecIso R).inv ≫ δ.hom.app (op d) ≫
          c.ι.app (E.functor.obj (op d)) = ρ := by
        simpa only [Category.assoc] using
          (congrArg (fun f ↦ f ≫ c.ι.app (E.functor.obj (op d))) htrip).trans (hρ _)
      have hleg : cn.ι.app (op b) ≫ t.hom =
          δ.hom.app (op d) ≫ c.ι.app (E.functor.obj (op d)) := ht (op d)
      have hring : (ΓSpecIso R).inv ≫
          colimit.ι D (op b) ≫ cmp₀.inv = ρ ≫ ringIso.inv := by
        apply (cancel_mono ringIso.hom).1
        simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
        change (ΓSpecIso R).inv ≫
          colimit.ι D (op b) ≫ cmp₀.inv ≫ cmp.hom ≫ t.hom = ρ
        calc
          _ = (ΓSpecIso R).inv ≫ cn.ι.app (op b) ≫ t.hom := by
            simpa only [Category.assoc] using
              congrArg (fun z ↦ (ΓSpecIso R).inv ≫ z ≫ t.hom) hcmp
          _ = ρ := by rw [hleg]; exact hρchart
      have hstr := strictLocalizationCone_π_app_hom s b
      change Spec.map (colimit.ι D (op b)) ≫
        (Spec R).isoSpec.inv ≫ i = strictLocalizationToBase s at hstr
      rw [isoSpec_Spec_inv] at hstr
      calc
        Spec.map (ρ ≫ ringIso.inv) ≫ i =
            Spec.map (colimit.ι D (op b) ≫ cmp₀.inv) ≫
              Spec.map (ΓSpecIso R).inv ≫ i := by
          simpa only [Spec.map_comp, Category.assoc] using
            congrArg (fun f ↦ Spec.map f ≫ i) hring.symm
        _ = Spec.map cmp₀.inv ≫ strictLocalizationToBase s := by
          simp only [Spec.map_comp, Category.assoc]
          simpa only [Category.assoc] using
            congrArg (fun f ↦ Spec.map cmp₀.inv ≫ f) hstr
        _ = _ := hbase
    -- Shrink the chart category using its equivalence with affine neighbourhoods.
    have : EssentiallySmall.{u} P.FullSubcategory :=
      essentiallySmall_of_fully_faithful
        (incl.asEquivalence.inverse ⋙
          (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).functor)
    have : EssentiallySmall.{u} Q.FullSubcategory :=
      essentiallySmall_of_fully_faithful Q.ι
    have : EssentiallySmall.{u} (Q.FullSubcategory)ᵒᵖ := inferInstance
    let H := (equivSmallModel.{u} (Q.FullSubcategory)ᵒᵖ).inverse ⋙ E.functor
    have : IsFiltered (SmallModel.{u} (Q.FullSubcategory)ᵒᵖ) :=
      IsFiltered.of_equivalence
        ((equivSmallModel.{u} (Q.FullSubcategory)ᵒᵖ).symm.trans E).symm
    let ca := c.whisker H
    have hca : IsColimit ca := (Functor.Final.isColimitWhiskerEquiv H c).symm hc
    -- Transport the ring colimit to A along the given spectrum isomorphism.
    let eRing : strictHenselizationRing s ≅ CommRingCat.of A :=
      { hom := Spec.preimage e.hom
        inv := Spec.preimage e.inv
        hom_inv_id := by
          apply Spec.map_injective
          simp
        inv_hom_id := by
          apply Spec.map_injective
          simp }
    let isoA : c.pt ≅ CommRingCat.of A := ringIso.symm ≪≫ eRing
    let caA := ca.extend isoA.hom
    have hcaA : IsColimit caA := hca.ofIsoColimit (ca.extendIso isoA)
    let α : (Functor.const _).obj R ⟶ H ⋙
        etaleResidueTriplesRingDiagram R p K
          (CommRingCat.ofHom (algebraMap F K)) :=
      { app := fun j ↦ (H.obj j).α
        naturality := fun j k f ↦ by
          have h := congrArg Over.Hom.left (Under.w (H.map f).hom)
          change (H.obj j).α ≫ (H.map f).hom.right.left = (H.obj k).α at h
          change (𝟙 R) ≫ (H.obj k).α = (H.obj j).α ≫ (H.map f).hom.right.left
          simpa only [Category.id_comp] using h.symm }
    -- Cancellation through the open immersion fixes the algebra structure.
    have hmap : ρ ≫ isoA.hom = CommRingCat.ofHom a := by
      apply Spec.map_injective
      apply (cancel_mono i).1
      simp only [isoA, Iso.trans_hom, Iso.symm_hom, Spec.map_comp,
        Category.assoc, eRing, Spec.map_preimage]
      rw [← Category.assoc (Spec.map ringIso.inv), ← Spec.map_comp, hstrmap]
      exact ha.symm
    -- The resulting compatible filtered etale presentation is exactly ind-etaleness.
    change a.IndEtale
    apply (RingHom.IndEtale.iff_exists (CommRingCat.ofHom a)).2
    refine ⟨_, inferInstance, inferInstance, H ⋙
      etaleResidueTriplesRingDiagram R p K
        (CommRingCat.ofHom (algebraMap F K)), α, caA.ι, hcaA, ?_⟩
    intro j
    refine ⟨?_, ?_⟩
    · have := (H.obj j).etale
      exact (HasRingHomProperty.Spec_iff (P := @Etale)).1 inferInstance
    · change (H.obj j).α ≫ c.ι.app (H.obj j) ≫ isoA.hom = _
      rw [← Category.assoc, hρ, hmap]

end AlgebraicGeometry.Scheme
