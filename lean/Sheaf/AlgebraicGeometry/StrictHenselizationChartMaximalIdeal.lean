/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import Sheaf.RingTheory.StrictHenselizationTriples
import Sheaf.AlgebraicGeometry.StrictHenselization
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap

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
  -- Compare the small-model colimit defining the ring with the full affine colimit `cn`.
  let G := (equivSmallModel.{u} (strictHenselizationNeighbourhoods s)).inverse ⋙
    strictHenselizationAffineInclusion s
  have : (strictHenselizationAffineInclusion s).IsEquivalence :=
    strictHenselizationAffineInclusion_isEquivalence s
  let eN : cn.pt ≅ strictHenselizationRing s :=
    ((Functor.Final.isColimitWhiskerEquiv G.op cn).symm hcn).coconePointUniqueUpToIso
      (colimit.isColimit (strictHenselizationAffineDiagram s))
  have hleg (j : SmallModel.{u} (strictHenselizationNeighbourhoods s)) :
      cn.ι.app (op (G.obj j)) ≫ eN.hom = colimit.ι (strictHenselizationAffineDiagram s) (op j) :=
    IsColimit.comp_coconePointUniqueUpToIso_hom
      ((Functor.Final.isColimitWhiskerEquiv G.op cn).symm hcn)
      (colimit.isColimit (strictHenselizationAffineDiagram s)) (op j)
  let e₁ : strictHenselizationRing s ≅ cn.pt := eN.symm
  let e₂ : ct.pt ≅ c.pt := hct.coconePointUniqueUpToIso hc
  let e : strictHenselizationRing s ≅ c.pt := e₁ ≪≫ t ≪≫ e₂
  let chart : N := ⟨⟨Etale.mk i, Over.homMk xR rfl⟩, inferInstanceAs (IsAffine (Spec R))⟩
  let chartU : Q.FullSubcategory := ⟨chart, 𝟙 _, by simp [chart]⟩
  let j := G.objPreimage chart
  let φ : G.obj j ⟶ chart := (G.objObjPreimageIso chart).hom
  let ι0 : D.obj (op chart) ⟶ strictHenselizationRing s :=
    D.map φ.op ≫ colimit.ι (strictHenselizationAffineDiagram s) (op j)
  have hι0 : ι0 ≫ e₁.hom = cn.ι.app (op chart) := by
    have h := hleg j
    have h' : colimit.ι (strictHenselizationAffineDiagram s) (op j) ≫ eN.inv =
        cn.ι.app (op (G.obj j)) := by
      rw [← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    simp only [ι0, e₁, Iso.symm_hom, Category.assoc]
    rw [h']
    exact cn.w φ.op
  have he : ι0 ≫ e.hom = cn.ι.app (op chart) ≫ t.hom ≫ e₂.hom := by
    simp only [e, Iso.trans_hom, ← Category.assoc]
    rw [hι0]
  have hchart :
      (ΓSpecIso R).inv ≫ ι0 ≫ e.hom = ρ := by
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
      (ΓSpecIso R).inv ≫ ι0 = ρ ≫ e.inv := by
    apply (cancel_mono e.hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hchart
  let : IsLocalRing (strictHenselizationRing s) := e.symm.commRingCatIsoToRingEquiv.isLocalRing
  refine ⟨inferInstance, ρ ≫ e.inv, ?_, ?_⟩
  · rw [← hchart', Spec.map_comp]
    -- the underlying scheme map of `φ`, a map over `S` into the chart `Spec R`
    let B := ((equivSmallModel.{u}
      (strictHenselizationNeighbourhoods s)).inverse.obj j).1.left.unop
    let u : Spec B ⟶ Spec R := φ.hom.1.left
    have hu : u ≫ i = (G.obj j).obj.1.hom := MorphismProperty.Over.w φ.hom.1
    have hn := Scheme.toSpecΓ_naturality u
    have hn' := congrArg
      (fun z ↦ Spec.map (ΓSpecIso B).inv ≫ z ≫ Spec.map (ΓSpecIso R).inv) hn
    simp only [Category.assoc, SpecMap_ΓSpecIso_inv_toSpecΓ_assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id] at hn'
    simp only [ι0, Spec.map_comp, Category.assoc]
    change (strictHenselizationCone s).π.app (op (op j)) ≫ Spec.map u.appTop ≫
      Spec.map (ΓSpecIso R).inv ≫ i = _
    rw [← Category.assoc (Spec.map u.appTop), ← hn', Category.assoc, hu]
    exact strictHenselizationStructuralMap_eq s j
  · have h := IsLocalRing.map_ringEquiv_maximalIdeal e.symm.commRingCatIsoToRingEquiv
    change (IsLocalRing.maximalIdeal c.pt).map e.inv.hom = _ at h
    rw [hm, hk, Ideal.map_map] at h
    exact h.symm

end AlgebraicGeometry.Scheme
