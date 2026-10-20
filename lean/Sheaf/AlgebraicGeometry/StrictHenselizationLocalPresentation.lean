/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U2, SHEAF group J4, SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.RingTheory.IsStrictHenselization
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.EtaleResidueTriplesLocalizedStrictHenselization

/-! # Geometric strict henselization as a local-base algebra

Source: Stacks Project, Tag 04HX (lemma-describe-etale-local-ring).
(blueprint: lem-sbc-geometric-strict-henselization-local-presentation)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

set_option maxHeartbeats 800000 in
-- The nested representative, affine-chart and triple diagrams require extra elaboration.
set_option backward.isDefEq.respectTransparency false in
/-- The geometric strict henselization is an algebraic strict henselization of a prime
localization, compatibly with the given structural ring map. There is no divisor here.
Source: Stacks Project, Tag 04HX (lemma-describe-etale-local-ring), using Tag 04GW.
(blueprint: lem-sbc-geometric-strict-henselization-local-presentation)

Proof: Let q be the image of the geometric point, and put A = R_q. Its residue field is
canonically the residue field at q. Inside the geometric field take the relative separable
closure K of that residue field. Affine pointed etale neighbourhoods compute the geometric
strict henselization ring. By the affine neighbourhood/triples comparison their coordinate
ring diagram is equivalent to etale residue triples over R at q with embeddings into K.
Passing from R to A does not change its colimit: etale algebras and their finitely many
presentation equations descend from A to R after inverting one element outside q, and
these principal localizations are pointed etale neighbourhoods. The equivalence between
residue triples over the local ring A and etale A-algebras pointed in K identifies this
colimit with the diagram defining Algebra.IsStrictHenselization. Each element outside q
is a unit in the colimit, so the structural R-map extends uniquely to A. The comparison
preserves the maps from R; applying the faithful spectrum functor and hb identifies that
R-map with b. Transport the A-algebra structure through the colimit ring isomorphism;
its composite with R -> A is therefore b. All colimit identifications are characterized
by their legs, so no arbitrary algebraic object is chosen from mere existence. -/
theorem strictHenselizationRing_local_presentation
    (R : CommRingCat.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselizationRing barY)
    (hb : Spec.map b = strictHenselizationStructuralMap barY) :
    ∃ (q : Ideal R) (_ : q.IsPrime)
      (K : Type u) (_ : Field K)
      (_ : Algebra (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : IsSepClosure (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : Algebra (Localization.AtPrime q) K)
      (_ : IsScalarTower (Localization.AtPrime q)
        (IsLocalRing.ResidueField (Localization.AtPrime q)) K)
      (_ : Algebra (Localization.AtPrime q) (strictHenselizationRing barY)),
      (∀ r : R, algebraMap (Localization.AtPrime q) (strictHenselizationRing barY)
        (algebraMap R (Localization.AtPrime q) r) = b.hom r) ∧
      Algebra.IsStrictHenselization (Localization.AtPrime q) K
        (strictHenselizationRing barY) := by
  classical
  let p := (SpecToEquivOfField Ω (Spec R) barY).1
  let F := (Spec R).residueField p
  let : Algebra F Ω := (SpecToEquivOfField Ω (Spec R) barY).2.hom.toAlgebra
  let K := separableClosure F Ω
  let χ := CommRingCat.ofHom (algebraMap F K)
  let P : ObjectProperty (pointSmallEtale barY).fiber.Elements :=
    fun c ↦ IsAffine c.1.left
  let Q : ObjectProperty P.FullSubcategory :=
    fun c ↦ ∃ g : c.obj.1.left ⟶ Spec R, g ≫ 𝟙 (Spec R) = c.obj.1.hom
  have h := etale_local_ring_triples (Spec R) Ω R (𝟙 (Spec R)) barY
  rw [Category.comp_id] at h
  obtain ⟨-, -, -, -, E, δ, hE, cn, -, ct,
    ⟨hcn⟩, -, ⟨hct⟩, -, s, -, hs⟩ := h
  let G := (equivSmallModel.{u} (strictHenselizationNeighbourhoods barY)).inverse ⋙
    strictHenselizationAffineInclusion barY
  have : (strictHenselizationAffineInclusion barY).IsEquivalence :=
    strictHenselizationAffineInclusion_isEquivalence barY
  let k : Cocone (strictHenselizationAffineDiagram barY) :=
    colimit.cocone (strictHenselizationAffineDiagram barY)
  have hk : IsColimit k := colimit.isColimit _
  -- Specify the cocone before Lean infers it from the reducible colimit vertex.
  let eN : cn.pt ≅ strictHenselizationRing barY :=
    ((Functor.Final.isColimitWhiskerEquiv G.op cn).symm hcn).coconePointUniqueUpToIso
      (t := k) hk
  have hleg (j : SmallModel.{u} (strictHenselizationNeighbourhoods barY)) :
      cn.ι.app (op (G.obj j)) ≫ eN.hom = k.ι.app (op j) :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ (t := k) hk (op j)
  let e : ct.pt ≅ strictHenselizationRing barY := s.symm ≪≫ eN
  -- The identity triple determines the common structural map from R.
  let t0 : EtaleResidueTriples R p K χ :=
    ⟨R, 𝟙 R, inferInstance, p, by simp, χ, by simp⟩
  let b' : R ⟶ strictHenselizationRing barY := ct.ι.app t0 ≫ e.hom
  have hbase (t : EtaleResidueTriples R p K χ) : t.α ≫ ct.ι.app t ≫ e.hom = b' := by
    let f : t0 ⟶ t := InducedCategory.homMk
      (Under.homMk (Over.homMk t.α t.compatible) (by
        apply Over.OverMorphism.ext
        change (𝟙 R) ≫ t.α = t.α
        simp))
    exact congrArg (fun z ↦ z ≫ e.hom) (ct.w f)
  let := (strictHenselization_properties barY).2.1
  let j := Classical.choice (IsCofiltered.nonempty (C :=
    SmallModel.{u} (strictHenselizationNeighbourhoods barY)))
  let c : Q.FullSubcategory := ⟨G.obj j, (G.obj j).obj.1.hom, by simp⟩
  have hα := (hE c).1 (G.obj j).obj.1.hom (by rfl)
  have hmap : b' = (ΓSpecIso R).inv ≫ (G.obj j).obj.1.hom.appTop ≫
      k.ι.app (op j) := by
    rw [← hbase (E.functor.obj (op c)), ← hα]
    simp only [Category.assoc]
    rw [← Category.assoc (δ.hom.app (op c)), ← hs (op c)]
    simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Iso.hom_inv_id_assoc]
    change (ΓSpecIso R).inv ≫ (G.obj j).obj.1.hom.appTop ≫
      (cn.ι.app (op (G.obj j)) ≫ eN.hom) = _
    rw [hleg]
  -- Check the map on a representative, then use faithfulness of Spec.
  have hstruct : Spec.map b' = strictHenselizationStructuralMap barY := by
    rw [hmap, Spec.map_comp, Spec.map_comp]
    let B := ((equivSmallModel.{u}
      (strictHenselizationNeighbourhoods barY)).inverse.obj j).1.left.unop
    let g : Spec B ⟶ Spec R := (G.obj j).obj.1.hom
    have hn := Scheme.toSpecΓ_naturality g
    have hn' := congrArg
      (fun z ↦ Spec.map (ΓSpecIso B).inv ≫ z ≫ Spec.map (ΓSpecIso R).inv) hn
    simp only [Category.assoc, SpecMap_ΓSpecIso_inv_toSpecΓ_assoc,
      toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id] at hn'
    change (strictHenselizationCone barY).π.app (op (op j)) ≫
      Spec.map g.appTop ≫ Spec.map (ΓSpecIso R).inv = _
    rw [← hn']
    exact strictHenselizationStructuralMap_eq barY j
  have hb' : b' = b := Spec.map_injective (hstruct.trans hb.symm)
  obtain ⟨L, hL, ares, hsep, aL, htower, aH, hcomp, hstrict⟩ :=
    etaleResidueTriples_localized_isStrictHenselization R p K ct hct
      (strictHenselizationRing barY) e b' hbase
  refine ⟨p.asIdeal, inferInstance, L, hL, ares, hsep, aL, htower, aH, ?_, hstrict⟩
  intro x
  exact (hcomp x).trans (congrArg (fun f : R ⟶ strictHenselizationRing barY ↦ f.hom x) hb')

end AlgebraicGeometry.Scheme
