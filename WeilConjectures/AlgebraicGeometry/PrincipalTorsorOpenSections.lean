/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PrincipalTorsorComparisons.PrincipalTorsorSignTypes
public import WeilConjectures.AlgebraicGeometry.EtaleOpenCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMapEtale
import all WeilConjectures.SmoothPurity.OpenClosedIntegralSections
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement

/-! # Uniqueness of normalized open sections
Source: Stacks 03F3, the open adjunction and its normalization on one.
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

private def canonicalOpenEquiv {D T : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] (W : T.Opens)
    (_h : Set.range i.base = (Set.range W.ι.base)ᶜ)
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ((openImmersionLowerShriek AddCommGrpCat.{u + 1} W.ι).obj
      ((upperStar AddCommGrpCat.{u + 1} W.ι).obj (supportedIntegralConstant T)) ⟶ G) ≃
      G.obj.obj (op (Scheme.Etale.mk W.ι)) :=
  ((openImmersionLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1} W.ι).homEquiv
    ((upperStar AddCommGrpCat.{u + 1} W.ι).obj (supportedIntegralConstant T)) G).trans
    ((Iso.homCongr
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} W.ι).app
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)))
      ((upperStarIsoOpenImmersionRestriction AddCommGrpCat.{u + 1} W.ι).app G)).trans
      (EtaleOpenComparison.restrictedSectionsEquiv W.ι G).toEquiv)

set_option maxRecDepth 4096 in
private theorem canonicalOpenEquiv_natural {D T : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] (W : T.Opens)
    (h : Set.range i.base = (Set.range W.ι.base)ᶜ)
    {G H : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}} (f : G ⟶ H)
    (a : (openImmersionLowerShriek AddCommGrpCat.{u + 1} W.ι).obj
      ((upperStar AddCommGrpCat.{u + 1} W.ι).obj (supportedIntegralConstant T)) ⟶ G) :
    canonicalOpenEquiv i W h H (a ≫ f) =
      f.hom.app (op (Scheme.Etale.mk W.ι)) (canonicalOpenEquiv i W h G a) := by
  let cZ := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} W.ι).app
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let c := upperStarIsoOpenImmersionRestriction AddCommGrpCat.{u + 1} W.ι
  let adj := openImmersionLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1} W.ι
  change EtaleOpenComparison.restrictedSectionsEquiv W.ι H
    (cZ.inv ≫ adj.homEquiv _ _ (a ≫ f) ≫ c.hom.app H) =
      f.hom.app (op (Scheme.Etale.mk W.ι))
        (EtaleOpenComparison.restrictedSectionsEquiv W.ι G
          (cZ.inv ≫ adj.homEquiv _ _ a ≫ c.hom.app G))
  rw [Adjunction.homEquiv_naturality_right, Category.assoc, c.hom.naturality]
  simpa only [Category.assoc] using
    (EtaleOpenComparison.restrictedSectionsEquiv_naturality W.ι f
      (cZ.inv ≫ adj.homEquiv _ _ a ≫ c.hom.app G))

set_option maxRecDepth 4096 in
private theorem canonicalOpenEquiv_one {D T : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] (W : T.Opens)
    (h : Set.range i.base = (Set.range W.ι.base)ᶜ) :
    canonicalOpenEquiv i W h (supportedIntegralConstant T)
      (principalTorsorLocalization i W h).f =
        torsorExtensionOne T (Scheme.Etale.mk W.ι) := by
  let M := AddCommGrpCat.of (ULift.{u + 1} ℤ)
  let e := Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} W.ι
  let c := upperStarIsoOpenImmersionRestriction AddCommGrpCat.{u + 1} W.ι
  have hB : (constantSheafAdj W.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}
      terminalIsTerminal).homEquiv _ _ (e.inv.app M ≫ c.hom.app _) =
    (constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
      terminalIsTerminal).unit.app M ≫ (supportedIntegralConstant T).obj.map
        (terminal.from ((MorphismProperty.Over.map ⊤ (inferInstance : Etale W.ι)).obj
          (⊤_ W.toScheme.Etale))).op := by
    rw [Adjunction.homEquiv_naturality_right]
    simp only [e, Scheme.upperStarConstantSheafIso, Adjunction.leftAdjointUniq_inv_app,
      Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [← unit_app_comp_lowerStarCompSheafSectionsTerminalIso_hom_app_comp W.ι
      (inferInstance : Etale W.ι)]
    simp [Adjunction.comp_unit_app]
    rfl
  change EtaleOpenComparison.restrictedSectionsEquiv W.ι _
    (e.inv.app M ≫
      (openImmersionLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1} W.ι).homEquiv
        _ _ ((openImmersionLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1}
          W.ι).counit.app _) ≫ c.hom.app _) = _
  have hε := (openImmersionLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1}
    W.ι).right_triangle_components (supportedIntegralConstant T)
  erw [Adjunction.homEquiv_unit]
  erw [hε, Category.id_comp]
  rw [restrictedSectionsEquiv_apply]
  have hb := ConcreteCategory.congr_hom hB (ULift.up 1)
  rw [constantSheafAdj_homEquiv_apply] at hb
  simp only [ConcreteCategory.comp_apply] at hb
  let V := Scheme.Etale.mk (𝟙 W.toScheme)
  let a := e.inv.app M ≫ c.hom.app (supportedIntegralConstant T)
  let q : V ⟶ ⊤_ W.toScheme.Etale := terminal.from V
  let z := toSheafify W.toScheme.smallEtaleTopology
    ((Functor.const W.toScheme.Etaleᵒᵖ).obj M)
  have hn := NatTrans.naturality_apply a.hom q.op (z.app (op (⊤_ _)) (ULift.up 1))
  have hz := NatTrans.naturality_apply z q.op (ULift.up 1)
  change z.app (op V) (ULift.up 1) =
    ((constantSheaf W.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M).obj.map
      q.op (z.app (op (⊤_ _)) (ULift.up 1)) at hz
  have ha : a.hom.app (op V) (z.app (op V) (ULift.up 1)) =
      ((openImmersionRestriction AddCommGrpCat.{u + 1} W.ι).obj
        (supportedIntegralConstant T)).obj.map q.op
          ((supportedIntegralConstant T).obj.map
            (terminal.from ((MorphismProperty.Over.map ⊤ (inferInstance : Etale W.ι)).obj
              (⊤_ W.toScheme.Etale))).op
            (((constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
              terminalIsTerminal).unit.app M) (ULift.up 1))) := by
    erw [← hz] at hn
    exact hn.trans (congrArg (fun x =>
      ((openImmersionRestriction AddCommGrpCat.{u + 1} W.ι).obj
        (supportedIntegralConstant T)).obj.map q.op x) hb)
  erw [ha]
  change (supportedIntegralConstant T).obj.map _
    ((supportedIntegralConstant T).obj.map _
      ((supportedIntegralConstant T).obj.map _ _)) = _
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply]
  exact (NatTrans.naturality_apply
    (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj M)) _
      (ULift.up 1)).symm

private theorem gmRestrictionComparison {U T : Scheme.{u}} (j : U ⟶ T)
    [IsOpenImmersion j] :
    (upperStarIsoOpenImmersionRestriction AddCommGrpCat.{u + 1} j).hom.app T.gmSheaf =
      Scheme.upperStarGmSheafToGmSheaf j := by
  let adj := localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} j
    (inferInstance : Etale j)
  have h : Scheme.upperStarGmSheafToGmSheaf j =
      (upperStarIsoOpenImmersionRestriction AddCommGrpCat.{u + 1} j).hom.app T.gmSheaf ≫
        (adj.homEquiv _ _).symm (Scheme.gmSheafToLowerStarGmSheaf j) := by
    rw [Scheme.upperStarGmSheafToGmSheaf, Adjunction.homEquiv_counit,
      Adjunction.homEquiv_counit, upperStarIsoOpenImmersionRestriction,
      ← Adjunction.leftAdjointUniq_hom_app_counit _ adj, NatTrans.naturality_assoc]
    rfl
  rw [h]
  suffices (adj.homEquiv _ _).symm (Scheme.gmSheafToLowerStarGmSheaf j) = 𝟙 _ by
    rw [this]
    erw [Category.comp_id]
  ext V x
  have hm : ((adj.homEquiv _ _).symm (Scheme.gmSheafToLowerStarGmSheaf j)).hom.app V =
      CommRingCat.unitsAddCommGrpULift.{u + 1, u}.map (𝟙 _) := by
    change CommRingCat.unitsAddCommGrpULift.{u + 1, u}.map _ ≫
      CommRingCat.unitsAddCommGrpULift.{u + 1, u}.map _ ≫ 𝟙 _ = _
    rw [Category.comp_id, ← Functor.map_comp]
    congr 1
    change Scheme.Γ.map _ ≫ Scheme.Γ.map _ = _
    rw [← Functor.map_comp]
    refine (congrArg Scheme.Γ.map ?_).trans (Scheme.Γ.map_id _)
    apply Quiver.Hom.unop_inj
    exact pullback.lift_fst _ _ _
  rw [hm, CategoryTheory.Functor.map_id]
  rfl

set_option maxRecDepth 4096 in
/-- Normalization on one uniquely fixes the open sections adjunction.
Source: Stacks 03F3 (blueprint: lem-pur-principal-torsor-open-sections).
Proof: compare the two representing equivalences by Yoneda. Their comparison
endomorphism fixes the localization inclusion, since both send it to one.
That inclusion is monic, so the endomorphism is the identity. Naturality then
identifies the two equivalences on every target and every map. -/
private theorem principalTorsorOpenSections (C : PrincipalTorsorComparisons.{u})
    (hC : C.Normalized) {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (W : T.Opens) (h : Set.range i.base = (Set.range W.ι.base)ᶜ)
    (G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (a : (openImmersionLowerShriek AddCommGrpCat.{u + 1} W.ι).obj
      ((upperStar AddCommGrpCat.{u + 1} W.ι).obj (supportedIntegralConstant T)) ⟶ G) :
    C.openSection T D i W h G a =
      EtaleOpenComparison.restrictedSectionsEquiv W.ι G
        (((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} W.ι).app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv ≫
          (openImmersionLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1}
            W.ι).homEquiv _ _ a ≫
          (upperStarIsoOpenImmersionRestriction AddCommGrpCat.{u + 1} W.ι).hom.app G) := by
  let Q := (principalTorsorLocalization i W h).X₁
  let p := (principalTorsorLocalization i W h).f
  let q : Q ⟶ Q := (canonicalOpenEquiv i W h Q).symm
    (C.openSection T D i W h Q (𝟙 Q))
  have hq : q ≫ p = p := by
    apply (canonicalOpenEquiv i W h _).injective
    rw [canonicalOpenEquiv_natural, Equiv.apply_symm_apply]
    rw [← hC.1 T D i W h Q _ p (𝟙 Q), Category.id_comp]
    exact (hC.2.1 T D i W h).trans (canonicalOpenEquiv_one i W h).symm
  have hp : Mono p := (shortExact_openClosedShortComplex AddCommGrpCat.{u + 1}
    W.ι i (supportedIntegralConstant T) h).mono_f
  have hqid : q = 𝟙 Q := (cancel_mono p).1 (hq.trans (Category.id_comp p).symm)
  change _ = canonicalOpenEquiv i W h G a
  calc
    C.openSection T D i W h G a =
        a.hom.app (op (Scheme.Etale.mk W.ι))
          (C.openSection T D i W h Q (𝟙 Q)) := by
      have hn := hC.1 T D i W h Q G a (𝟙 Q)
      erw [Category.id_comp] at hn
      exact hn
    _ = a.hom.app (op (Scheme.Etale.mk W.ι))
        (canonicalOpenEquiv i W h Q q) := by rw [Equiv.apply_symm_apply]
    _ = canonicalOpenEquiv i W h G (q ≫ a) :=
      (canonicalOpenEquiv_natural i W h a q).symm
    _ = canonicalOpenEquiv i W h G a := by
      rw [hqid]
      erw [Category.id_comp]

set_option maxRecDepth 4096 in
/-- The normalized open adjunction sends a unit to its adjoint global morphism.
Source: Stacks 03F3 and 03PL (blueprint: lem-pur-principal-torsor-open-sections).
Proof: apply the unique normalized sections equivalence. The adjunction triangle
cancels the counit, the inverse-image constant comparisons cancel, and the etale
comparison on the multiplicative group is literal restriction. Evaluation of the
remaining degree-zero cohomology class is the original unit. -/
theorem principalTorsorOpenUnit (C : PrincipalTorsorComparisons.{u})
    (hC : C.Normalized) {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (W : T.Opens) (h : Set.range i.base = (Set.range W.ι.base)ᶜ)
    (s : Γ(W.toScheme, ⊤)ˣ) :
    (C.openSection T D i W h T.gmSheaf).symm ⟨Additive.ofMul s⟩ =
      (openImmersionLowerShriek AddCommGrpCat.{u + 1} W.ι).map
        (((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} W.ι).app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom ≫
          Ext.addEquiv₀ ((Sheaf.H.equiv₀ W.toScheme.gmSheaf
            (MorphismProperty.Over.mkIdTerminal @Etale W.toScheme)).symm
              ⟨Additive.ofMul s⟩) ≫ (Scheme.upperStarGmSheafIso W.ι).inv) ≫
        (openImmersionLowerShriekUpperStarAdjunction AddCommGrpCat.{u + 1}
          W.ι).counit.app T.gmSheaf := by
  apply (C.openSection T D i W h T.gmSheaf).injective
  rw [AddEquiv.apply_symm_apply, principalTorsorOpenSections C hC]
  symm
  erw [← Adjunction.homEquiv_counit, Equiv.apply_symm_apply]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  erw [gmRestrictionComparison]
  dsimp only [Scheme.upperStarGmSheafIso, asIso_inv]
  erw [IsIso.inv_hom_id, Category.comp_id]
  rw [restrictedSectionsEquiv_apply]
  let x := (Sheaf.H.equiv₀ W.toScheme.gmSheaf
    (MorphismProperty.Over.mkIdTerminal @Etale W.toScheme)).symm
      (show W.toScheme.gmSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 W.toScheme))) from
        ⟨Additive.ofMul s⟩)
  let v := Ext.addEquiv₀ x
  have hm : Ext.mk₀ v = x := Ext.addEquiv₀.symm_apply_apply _
  have heval : Sheaf.H.equiv₀ W.toScheme.gmSheaf
      (MorphismProperty.Over.mkIdTerminal @Etale W.toScheme) (Ext.mk₀ v) =
      v.hom.app (op (Scheme.Etale.mk (𝟙 W.toScheme)))
        ((toSheafify W.toScheme.smallEtaleTopology
          ((Functor.const W.toScheme.Etaleᵒᵖ).obj
            (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app
              (op (Scheme.Etale.mk (𝟙 W.toScheme))) (ULift.up 1)) := by
    simp only [Sheaf.H.equiv₀, AddEquiv.trans_apply]
    erw [Ext.addEquiv₀.apply_symm_apply]
    change ((constantSheafAdj W.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}
      (MorphismProperty.Over.mkIdTerminal @Etale W.toScheme)).homEquiv _ _ v)
        (ULift.up 1) = _
    rw [constantSheafAdj_homEquiv_apply]
    rfl
  have h0 := (Sheaf.H.equiv₀ W.toScheme.gmSheaf
    (MorphismProperty.Over.mkIdTerminal @Etale W.toScheme)).apply_symm_apply
      (show W.toScheme.gmSheaf.obj.obj (op (Scheme.Etale.mk (𝟙 W.toScheme))) from
        ⟨Additive.ofMul s⟩)
  change Sheaf.H.equiv₀ _ _ x = _ at h0
  rw [← hm, heval] at h0
  erw [h0]
  change CommRingCat.unitsAddCommGrpULift.{u + 1, u}.map
    (Scheme.Γ.map (𝟙 W.toScheme).op) (ULift.up (Additive.ofMul s)) = _
  erw [op_id, CategoryTheory.Functor.map_id]
  rfl

end AlgebraicGeometry.Etale
