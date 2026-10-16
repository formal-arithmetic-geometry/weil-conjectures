/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import Sheaf.RingTheory.StrictHenselizationTriples

/-! # The maximal ideal in an affine chart of the strict henselization

Source: Stacks Project, Tags 04HX, 04GW and 04GP.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option maxHeartbeats 800000 in
-- Comparing the nested chart, triple and small-model diagrams requires extra elaboration.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- In any affine open chart through which the geometric point factors, the structural
ring map extends the distinguished prime to the maximal ideal of the strict henselization.
Source: Stacks Project, Tag 04HX, using Tags 04GW and 04GP.
(blueprint: lem-weil-pbc-strict-henselization-chart-maximal-ideal)

Proof: restrict affine pointed neighbourhoods to those over the chart. This inclusion
is initial by the shrinking argument in Tag 04HX. Identify its opposite with the category
of etale residue triples over R, pointed in the relative separable closure of the residue
field of xR in Ω. The residue embeddings land in this closure because etale residue
extensions are finite separable. The coordinate-ring diagram comparison respects the
R-map on each object. Initiality, this diagram comparison, and the small representative
comparison give a canonical ring isomorphism from the chosen strict-henselization ring
to the triple colimit. Tags 04GW and 04GP say the latter is local with maximal ideal equal
to the extension of the distinguished prime. Transport its local-ring structure and
its R-map through this isomorphism. Ring isomorphisms carry maximal ideals and extended
ideals to the corresponding ideals, giving the displayed equality. On the chart
neighbourhood the coprojection defines the structure morphism; the comparison preserves
that coprojection, so the transported R-map has spectrum followed by i equal to the
chosen structural morphism. The assertion includes the field case; the triple colimit
has a field quotient, so it is nonzero even when a chart ring has zero divisors. -/
theorem strictHenselization_chart_maximalIdeal
    {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (R : CommRingCat.{u}) (i : Spec R ⟶ S) [IsOpenImmersion i]
    (xR : Spec (.of Ω) ⟶ Spec R) :
    ∃ (_ : IsLocalRing (strictHenselizationRing (xR ≫ i)))
      (ρ : R ⟶ strictHenselizationRing (xR ≫ i)),
      Spec.map ρ ≫ i = strictHenselizationStructuralMap (xR ≫ i) ∧
      IsLocalRing.maximalIdeal (strictHenselizationRing (xR ≫ i)) =
        (xR (IsLocalRing.closedPoint Ω)).asIdeal.map ρ.hom  := by
  classical
  let s := xR ≫ i
  let p := (SpecToEquivOfField Ω (Spec R) xR).1
  let F := (Spec R).residueField p
  let : Algebra F Ω := (SpecToEquivOfField Ω (Spec R) xR).2.hom.toAlgebra
  let K := separableClosure F Ω
  let P : ObjectProperty (pointSmallEtale s).fiber.Elements := fun c ↦ IsAffine c.1.left
  let N := P.FullSubcategory
  let Q : ObjectProperty N :=
    fun c ↦ ∃ g : c.obj.1.left ⟶ Spec R, g ≫ i = c.obj.1.hom
  let D := (P.ι ⋙ CategoryOfElements.π (pointSmallEtale s).fiber ⋙
    Etale.forget S ⋙ Over.forget S).op ⋙ Scheme.Γ
  obtain ⟨_, _, _, _, E, δ, hE, cn, _, ct,
    ⟨hcn⟩, _, ⟨hct⟩, _, t, _, ht⟩ :=
    etale_local_ring_triples S Ω R i xR
  obtain ⟨_, c, ⟨hc⟩, hlocal, ρ, _, hρ, _, _, hm, hk, _⟩ :=
    strictHenselization_triples R p K
  let : IsLocalRing c.pt := hlocal
  let : HasColimit D := by
    change HasColimit (strictHenselizationDiagram s)
    infer_instance
  let e₁ : strictHenselizationRing s ≅ cn.pt :=
    (colimit.isColimit D).coconePointUniqueUpToIso hcn
  let e₂ : ct.pt ≅ c.pt := hct.coconePointUniqueUpToIso hc
  let e : strictHenselizationRing s ≅ c.pt := e₁ ≪≫ t ≪≫ e₂
  have he (n : Nᵒᵖ) :
      colimit.ι D n ≫ e.hom = cn.ι.app n ≫ t.hom ≫ e₂.hom := by
    have h := (colimit.isColimit D).comp_coconePointUniqueUpToIso_hom hcn n
    change colimit.ι D n ≫ e₁.hom = cn.ι.app n at h
    simpa only [e, Iso.trans_hom, Category.assoc] using
      congrArg (fun a ↦ a ≫ t.hom ≫ e₂.hom) h
  let chart : N := ⟨⟨Etale.mk i, Over.homMk xR rfl⟩, inferInstanceAs (IsAffine (Spec R))⟩
  let chartU : Q.FullSubcategory := ⟨chart, 𝟙 _, by simp [chart]⟩
  have hchart :
      (ΓSpecIso R).inv ≫ colimit.ι D (op chart) ≫ e.hom = ρ := by
    rw [he]
    have ht' := ht (op chartU)
    change cn.ι.app (op chart) ≫ t.hom =
      δ.hom.app (op chartU) ≫ ct.ι.app (E.functor.obj (op chartU)) at ht'
    rw [← Category.assoc (cn.ι.app _), ht']
    have hα : (ΓSpecIso R).inv ≫ δ.hom.app (op chartU) =
        (E.functor.obj (op chartU)).α := by
      have hα := (hE chartU).1 (𝟙 _) (by simp [chartU, chart])
      change (ΓSpecIso R).inv ≫ (𝟙 Γ(Spec R, ⊤)) ≫ δ.hom.app (op chartU) =
        (E.functor.obj (op chartU)).α at hα
      rwa [Category.id_comp] at hα
    have hι := hct.comp_coconePointUniqueUpToIso_hom hc (E.functor.obj (op chartU))
    change ct.ι.app (E.functor.obj (op chartU)) ≫ e₂.hom =
      c.ι.app (E.functor.obj (op chartU)) at hι
    calc
      _ = (E.functor.obj (op chartU)).α ≫
          ct.ι.app (E.functor.obj (op chartU)) ≫ e₂.hom := by
        simpa only [Category.assoc] using
          congrArg (fun a ↦ a ≫ ct.ι.app (E.functor.obj (op chartU)) ≫ e₂.hom) hα
      _ = (E.functor.obj (op chartU)).α ≫ c.ι.app (E.functor.obj (op chartU)) := by
        rw [hι]
      _ = ρ := hρ _
  have hchart' :
      (ΓSpecIso R).inv ≫ colimit.ι D (op chart) = ρ ≫ e.inv := by
    apply (cancel_mono e.hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hchart
  let : IsLocalRing (strictHenselizationRing s) := e.symm.commRingCatIsoToRingEquiv.isLocalRing
  refine ⟨inferInstance, ρ ≫ e.inv, ?_, ?_⟩
  · rw [← hchart', Spec.map_comp]
    have h := strictLocalizationCone_π_app_hom s chart
    rw [strictLocalizationCone_π_app] at h
    change Spec.map (colimit.ι D (op chart)) ≫ inv (Spec R).toSpecΓ ≫ i = _ at h
    have hinv : inv (Spec R).toSpecΓ = Spec.map (ΓSpecIso R).inv := by
      apply (cancel_mono (Spec R).toSpecΓ).1
      simp only [IsIso.inv_hom_id, SpecMap_ΓSpecIso_inv_toSpecΓ]
    rwa [hinv] at h
  · have h := IsLocalRing.map_ringEquiv_maximalIdeal e.symm.commRingCatIsoToRingEquiv
    change (IsLocalRing.maximalIdeal c.pt).map e.inv.hom = _ at h
    rw [hm, hk, Ideal.map_map] at h
    exact h.symm

end AlgebraicGeometry.Scheme
