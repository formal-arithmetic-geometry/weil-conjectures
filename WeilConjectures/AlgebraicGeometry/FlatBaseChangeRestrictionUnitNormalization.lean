/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction

/-! # Normalizing the restricted tensor unit through a chart

Source: Stacks Project, Sheaves, Tags 0096 and 0097.
-/

@[expose] public section
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local irreducible] tensorPullback tensorPullbackObj

set_option maxHeartbeats 800000 in
-- The statement elaborates nested pullback and pushforward comparisons.
/-- The unit square pins the double transpose to the canonical pullback comparison.
Source: Stacks Project, Sheaves, Tags 0096 and 0097, adjunction and composition.

Proof: Let adj1 be the composite of restriction along a, pullback along t and
pullback along sigma; let adj2 be tensor pullback along p followed by restriction
along l. The commutative scheme equations identify their right adjoints by
rightIso. Uniqueness of left adjoints constructs the coefficient comparison k,
preceded by pullback of the inverse restriction/pullback comparison along a.
Transpose the desired equality through t and then restriction along a, after
precomposing with the restriction/pullback comparison along a. Naturality of the
hom-equivalences cancels that comparison. The unit equation for leftAdjointUniq
identifies the left side with the composite unit for adj2 followed by rightIso.inv.
Cancel rightIso.hom and evaluate at an open B of X. Expand the pushforward
composition and congruence comparisons and the restriction units. Apply the
given square at B, followed by restriction from u(u inverse(p inverse B)) to
l(l inverse(p inverse B)); this inclusion follows from l=j followed by u.
Functoriality combines the presheaf maps. All transports and restrictions on
each side are maps between the same opens and agree since opens form a thin
category. The resulting equation is exactly the evaluated desired equality.
Empty schemes, empty opens and zero modules obey these same identities.
No invertibility of the double transpose is asserted here. -/
theorem restriction_chart_unit_normalization
    {X X' Y Z L T : Scheme.{u}}
    (p : X' ⟶ X) (a : Y ⟶ X) (u : Z ⟶ X') (l : L ⟶ X')
    (j : L ⟶ Z) (q : Z ⟶ Y) (t : T ⟶ Y) (σ : L ≅ T)
    [IsOpenImmersion a] [IsOpenImmersion u] [IsOpenImmersion l]
    [IsOpenImmersion j]
    (eju : j ≫ u = l) (eqa : q ≫ a = u ≫ p) (ef : σ.hom ≫ t = j ≫ q)
    (F : X.Modules)
    (ψ : (restrictFunctor a).obj F ⟶
      (pushforward q).obj ((restrictFunctor u).obj ((tensorPullback p).obj F)))
    (square :
      (restrictAdjunction a).unit.app F ≫ (pushforward a).map ψ ≫
        (pushforwardComp q a).hom.app ((restrictFunctor u).obj ((tensorPullback p).obj F)) ≫
        (pushforwardCongr eqa).hom.app
          ((restrictFunctor u).obj ((tensorPullback p).obj F)) =
      (Classical.choose (exists_tensorPullbackAdjunction p)).unit.app F ≫
        (pushforward p).map ((restrictAdjunction u).unit.app ((tensorPullback p).obj F)) ≫
        (pushforwardComp u p).hom.app
          ((restrictFunctor u).obj ((tensorPullback p).obj F))) :
    let N := (pullback a).obj F
    let G := (tensorPullback p).obj F
    let M := (restrictFunctor l).obj G
    let c := (restrictFunctorComp j u).symm.app G ≪≫
      (restrictFunctorCongr eju).app G
    let r := (restrictAdjunction j).unit.app ((restrictFunctor u).obj G) ≫
      (pushforward j).map c.hom
    let b := ((restrictFunctorIsoPullback a).app F).inv ≫ ψ ≫
      (pushforward q).map r ≫ (pushforwardComp j q).hom.app M ≫
      (pushforwardCongr ef).inv.app M ≫ (pushforwardComp σ.hom t).inv.app M
    let e : (σ.hom ≫ t) ≫ a = l ≫ p := by
      rw [ef, Category.assoc, eqa, ← Category.assoc, eju]
    let rightIso : pushforward σ.hom ⋙ pushforward t ⋙ pushforward a ≅
        pushforward l ⋙ pushforward p :=
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (pushforwardComp σ.hom t) (pushforward a) ≪≫
        pushforwardComp (σ.hom ≫ t) a ≪≫ pushforwardCongr e ≪≫
        (pushforwardComp l p).symm
    let adj₁ := (restrictAdjunction a).comp
      ((pullbackPushforwardAdjunction t).comp (pullbackPushforwardAdjunction σ.hom))
    let adj₂ := (Classical.choose (exists_tensorPullbackAdjunction p)).comp
      (restrictAdjunction l)
    let k : (pullback σ.hom).obj ((pullback t).obj N) ≅ M :=
      (pullback σ.hom).mapIso ((pullback t).mapIso
        ((restrictFunctorIsoPullback a).symm.app F)) ≪≫
        (adj₁.leftAdjointUniq (adj₂.ofNatIsoRight rightIso.symm)).app F
    (pullbackPushforwardAdjunction σ.hom).homEquiv _ _ k.hom =
      ((pullbackPushforwardAdjunction t).homEquiv _ _).symm b := by
  intro N G M c r b e rightIso adj₁ adj₂ k
  apply ((pullbackPushforwardAdjunction t).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply]
  apply (cancel_epi ((restrictFunctorIsoPullback a).hom.app F)).mp
  apply ((restrictAdjunction a).homEquiv _ _).injective
  have hu := adj₁.homEquiv_leftAdjointUniq_hom_app
    (adj₂.ofNatIsoRight rightIso.symm) F
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app] at hu
  rw [← Adjunction.homEquiv_naturality_left,
    ← Adjunction.homEquiv_naturality_left]
  simp only [k, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Iso.symm_hom, ← Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [adj₁, Adjunction.comp_homEquiv] at hu
  change (restrictAdjunction a).homEquiv _ _
    ((pullbackPushforwardAdjunction t).homEquiv _ _
      ((pullbackPushforwardAdjunction σ.hom).homEquiv _ _
        ((adj₁.leftAdjointUniq (adj₂.ofNatIsoRight rightIso.symm)).hom.app F))) = _ at hu
  erw [hu]
  simp only [b, Adjunction.homEquiv_unit]
  simp only [Iso.app_inv, Iso.hom_inv_id_app_assoc]
  simp only [adj₂, Adjunction.comp_unit_app, Iso.symm_hom]
  apply (cancel_mono (rightIso.hom.app M)).mp
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  apply hom_ext
  intro B
  simp only [Hom.comp_app, pushforward_map_app, Functor.map_comp, rightIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    pushforwardComp_hom_app_app, pushforwardComp_inv_app_app,
    pushforwardCongr_hom_app_app, pushforwardCongr_inv_app_app,
    Category.id_comp, Category.comp_id]
  have hs := congrArg (fun z ↦ Hom.app z B) square
  simp only [Hom.comp_app, pushforward_map_app, pushforwardComp_hom_app_app,
    pushforwardCongr_hom_app_app] at hs
  erw [Category.comp_id] at hs
  erw [Category.id_comp] at hs
  repeat' erw [Category.id_comp]
  repeat' erw [Category.comp_id]
  simp only [r, c, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Hom.comp_app,
    pushforward_map_app, restrictAdjunction_unit_app_app,
    restrictFunctorComp_inv_app_app, restrictFunctorCongr_hom_app_app]
  have hl : l ''ᵁ (l ⁻¹ᵁ (p ⁻¹ᵁ B)) ≤ u ''ᵁ (u ⁻¹ᵁ (p ⁻¹ᵁ B)) := by
    rintro x ⟨y, hy, rfl⟩
    have ey : u (j y) = l y := congrArg (fun v : L ⟶ X' ↦ v y) eju
    refine ⟨j y, ?_, ey⟩
    change p (u (j y)) ∈ B
    rw [ey]
    exact hy
  have hh := congrArg (fun z ↦ z ≫ G.presheaf.map (homOfLE hl).op) hs
  simp only [restrictAdjunction_unit_app_app, restrict_map] at hh
  dsimp only [M] at *
  simp only [restrict_map]
  dsimp only [G] at hh ⊢
  repeat' erw [Category.assoc] at hh
  repeat' erw [Category.assoc]
  repeat' erw [← Functor.map_comp] at hh
  repeat' erw [← Functor.map_comp]
  convert hh.symm using 1

end AlgebraicGeometry.Scheme.Modules
