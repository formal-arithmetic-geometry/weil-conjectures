/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedIntegralModel
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectTransportComplete
import WeilConjectures.AlgebraicGeometry.Pbc.PbcDerivedScalarComplexUnit

/-! # Mates of coefficient tensor squares

Scalar extension along ring sheaves and restriction along ring sheaf isomorphisms satisfy the
pasting law of a pseudofunctor. The tensor comparison through a coefficient square is the mate
of the restriction square, and the transported scalar tensor squares compose as expected.

## Main statements

* `mateEquiv_tensorThroughCoefficientSquare_inv`: the mate of a tensor comparison through a
  coefficient square is the corresponding restriction square.
* `tensorThroughCoefficientSquare_paste`: pasting a tensor comparison through a coefficient
  square with scalar-extension compositors gives the tensor comparison of the pasted square.
* `integralTensorSquare_of_tensorThroughCoefficientSquare`: the resulting tensor square for
  isomorphisms given by transported tensor comparisons.
* `tensorThroughCoefficientSquare_inv_app_Q_of_tensorSection`: on a complex, the inverse tensor
  comparison through a coefficient square is the ordinary comparison fixed on tensor generators,
  read through the scalar-extension counits.

## Implementation details

Every comparison is identified with the mate of a comparison of derived restrictions. Pasting
of mates reduces the claim to the associativity of the restriction compositors.
On complexes, the mate is computed by the derived units, which the ordinary units compute on
every complex (`pbcDerivedScalarAdjunction_unit_app_Q`).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Functor
open WeilConjectures.LocallyFiniteAdicRealization WeilConjectures.AdicFiniteRealization

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- The inverse tensor comparison through a coefficient square, computed from the
scalar-extension units and counits. -/
theorem tensorThroughCoefficientSquare_inv_app
    {R P V T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (d : R ≅ P) (q : V ≅ T) (s : R ⟶ V) (c : P ⟶ T) (h : d.hom ≫ c = s ≫ q.hom) (K) :
    (tensorThroughCoefficientSquare X d q s c h).inv.app K =
      (pbcDerivedScalarAdjunction q.hom).unit.app
          ((pbcDerivedExtend s).obj ((pbcDerivedRestrict d.hom).obj K)) ≫
        (pbcDerivedRestrict q.hom).map
          ((coefficientExtensionSquare X d.hom c s q.hom h).inv.app
              ((pbcDerivedRestrict d.hom).obj K) ≫
            (pbcDerivedExtend c).map ((pbcDerivedScalarAdjunction d.hom).counit.app K)) := by
  unfold tensorThroughCoefficientSquare
  simp only [comp_obj, Iso.compInverseIso, Equivalence.invFunIdAssoc, Iso.trans_symm,
    Iso.symm_symm_eq, Iso.trans_assoc, isoWhiskerRight_trans, Iso.trans_inv, isoWhiskerLeft_inv,
    Iso.symm_inv, Category.assoc, isoWhiskerRight_inv, isoWhiskerRight_hom, whiskerRight_twice,
    NatTrans.comp_app, id_obj, rightUnitor_inv_app, whiskerLeft_app,
    Adjunction.toEquivalence_unitIso_hom_app, associator_inv_app, whiskerRight_app, map_id,
    associator_hom_app, Adjunction.toEquivalence_counitIso_hom_app, Functor.comp_map,
    leftUnitor_hom_app, Category.comp_id, Category.id_comp, map_comp]
  rfl

/-- A unit-counit composite through an equivalence has the conjugate of its middle comparison
as its mate. -/
private theorem mateEquiv_unit_comp_counit {A B C D : Type*} [Category* A] [Category* B]
    [Category* C] [Category* D] {Ld : A ⥤ B} {Rd : B ⥤ A} {Lc : B ⥤ D} {Rc : D ⥤ B}
    {Ls : A ⥤ C} {Rs : C ⥤ A} {Lq : C ⥤ D} {Rq : D ⥤ C}
    (ad : Ld ⊣ Rd) (ac : Lc ⊣ Rc) (as : Ls ⊣ Rs) (aq : Lq ⊣ Rq) (γ : Ls ⋙ Lq ⟶ Ld ⋙ Lc)
    (μ : TwoSquare Rd Lc Ls Rq) (hμ : ∀ K, μ.app K = aq.unit.app (Ls.obj (Rd.obj K)) ≫
      Rq.map (γ.app (Rd.obj K) ≫ Lc.map (ad.counit.app K))) :
    mateEquiv ac as μ = conjugateEquiv (ad.comp ac) (as.comp aq) γ := by
  ext Y
  simp [mateEquiv_apply, conjugateEquiv_apply_app, Adjunction.comp_unit_app,
    Adjunction.comp_counit_app, hμ]

/-- The mate of a tensor comparison through a coefficient square is the restriction square. -/
theorem mateEquiv_tensorThroughCoefficientSquare_inv
    {R P V T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (d : R ≅ P) (q : V ≅ T) (s : R ⟶ V) (c : P ⟶ T) (h : d.hom ≫ c = s ≫ q.hom) :
    mateEquiv (pbcDerivedScalarAdjunction c) (pbcDerivedScalarAdjunction s)
        (tensorThroughCoefficientSquare X d q s c h).inv =
      (derivedRestrictionSquare d.hom c q.hom s h).hom := by
  have e := Adjunction.conjugateEquiv_leftAdjointCompIso_inv (pbcDerivedScalarAdjunction d.hom)
    (pbcDerivedScalarAdjunction c)
    ((pbcDerivedScalarAdjunction s).comp (pbcDerivedScalarAdjunction q.hom))
    (derivedRestrictionSquare d.hom c q.hom s h)
  rw [← e]
  refine mateEquiv_unit_comp_counit _ _ _ _ _ _ fun K ↦ ?_
  rw [tensorThroughCoefficientSquare_inv_app]
  unfold coefficientExtensionSquare
  rfl


/-- Associativity of derived restriction compositors, in the form of the pasted square. -/
private theorem restrictComp_paste
    {PE OE ME ML Λ V PL OL : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (pE : PE ⟶ OE) (pL : PL ⟶ OL) (t : Λ ⟶ V)
    (rE : PE ⟶ ME) (rL : PL ⟶ ML) (cc : ME ⟶ ML) (legE : ME ⟶ Λ) (legL : ML ⟶ Λ)
    (hcoc : cc ≫ legL = legE) (kh : PE ⟶ PL) (hcs : kh ≫ rL = rE ≫ cc)
    (k : OE ⟶ OL) (cE : OE ⟶ V) (cL : OL ⟶ V) (hk : k ≫ cL = cE)
    (hθ : pE ≫ k = kh ≫ pL)
    (hmE : pE ≫ cE = (rE ≫ legE) ≫ t)
    (hmL : pL ≫ cL = (rL ≫ legL) ≫ t) (Y) :
    (pbcDerivedRestrictComp pE k (pE ≫ k) rfl).hom.app ((pbcDerivedRestrict cL).obj Y) ≫
      (pbcDerivedRestrictComp kh pL (pE ≫ k) hθ.symm).inv.app ((pbcDerivedRestrict cL).obj Y) ≫
      (pbcDerivedRestrict kh).map ((pbcDerivedRestrictComp pL cL (pL ≫ cL) rfl).hom.app Y) ≫
      (pbcDerivedRestrict kh).map
        ((pbcDerivedRestrictComp (rL ≫ legL) t (pL ≫ cL) hmL.symm).inv.app Y) ≫
      (pbcDerivedRestrict kh).map ((pbcDerivedRestrictComp rL legL (rL ≫ legL) rfl).inv.app
        ((pbcDerivedRestrict t).obj Y)) ≫
      (pbcDerivedRestrictComp kh rL (kh ≫ rL) rfl).hom.app
        ((pbcDerivedRestrict legL).obj ((pbcDerivedRestrict t).obj Y)) ≫
      (pbcDerivedRestrictComp rE cc (kh ≫ rL) hcs.symm).inv.app
        ((pbcDerivedRestrict legL).obj ((pbcDerivedRestrict t).obj Y)) ≫
      (pbcDerivedRestrict rE).map ((pbcDerivedRestrictComp cc legL legE hcoc).hom.app
        ((pbcDerivedRestrict t).obj Y)) =
    (pbcDerivedRestrict pE).map ((pbcDerivedRestrictComp k cL cE hk).hom.app Y) ≫
      (pbcDerivedRestrictComp pE cE (pE ≫ cE) rfl).hom.app Y ≫
      (pbcDerivedRestrictComp (rE ≫ legE) t (pE ≫ cE) hmE.symm).inv.app Y ≫
      (pbcDerivedRestrictComp rE legE (rE ≫ legE) rfl).inv.app ((pbcDerivedRestrict t).obj Y) := by
  let Φ := (pbcDerivedRestrictComp rE legE (rE ≫ legE) rfl).app ((pbcDerivedRestrict t).obj Y) ≪≫
    (pbcDerivedRestrictComp (rE ≫ legE) t (pE ≫ cE) hmE.symm).app Y
  rw [← cancel_mono Φ.hom]
  simp only [Φ, Iso.trans_hom, Iso.app_hom, Category.assoc, Iso.inv_hom_id_app_assoc,
    Iso.inv_hom_id_app, Category.comp_id]
  have e1 := pbcDerivedRestrictComp_assoc_app rE cc legL (kh ≫ rL) legE (rE ≫ legE)
    hcs.symm hcoc (by rw [hcs, Category.assoc, hcoc]) rfl ((pbcDerivedRestrict t).obj Y)
  have e2 := pbcDerivedRestrictComp_assoc_app kh rL legL (kh ≫ rL) (rL ≫ legL) (rE ≫ legE)
    rfl rfl (by rw [hcs, Category.assoc, hcoc]) (by rw [← Category.assoc, hcs,
      Category.assoc, hcoc]) ((pbcDerivedRestrict t).obj Y)
  have e3 := pbcDerivedRestrictComp_assoc_app kh (rL ≫ legL) t (rE ≫ legE) (pL ≫ cL)
    (pE ≫ cE) (by rw [← Category.assoc, hcs, Category.assoc, hcoc]) hmL.symm hmE.symm
    (by rw [hmL, ← Category.assoc, ← Category.assoc, hcs, Category.assoc rE, hcoc,
      ← hmE]) Y
  have e4 := pbcDerivedRestrictComp_assoc_app kh pL cL (pE ≫ k) (pL ≫ cL) (pE ≫ cE)
    hθ.symm rfl (by rw [Category.assoc, hk]) (by rw [← Category.assoc, ← hθ,
      Category.assoc, hk]) Y
  have e5 := pbcDerivedRestrictComp_assoc_app pE k cL (pE ≫ k) cE (pE ≫ cE)
    rfl hk (by rw [Category.assoc, hk]) rfl Y
  have c1 {𝒞 𝒟 ℰ : Type _} [Category 𝒞] [Category 𝒟] [Category ℰ] (H : 𝒟 ⥤ ℰ)
      {F G : 𝒞 ⥤ 𝒟} (e : F ≅ G) (P : 𝒞) {Z} (g : H.obj (G.obj P) ⟶ Z) :
      H.map (e.inv.app P) ≫ H.map (e.hom.app P) ≫ g = g := by
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
  rw [← reassoc_of% e1, Iso.inv_hom_id_app_assoc, reassoc_of% e2]
  rw [c1 (pbcDerivedRestrict kh) (pbcDerivedRestrictComp rL legL (rL ≫ legL) rfl)]
  rw [e3, c1 (pbcDerivedRestrict kh) (pbcDerivedRestrictComp (rL ≫ legL) t (pL ≫ cL) hmL.symm),
    ← e4, Iso.inv_hom_id_app_assoc, e5]

/-- The conjugate of a composite of scalar extensions along a restriction compositor is its
inverse. -/
private theorem conjugateEquiv_leftAdjointCompIso_hom {C₀ C₁ C₂ : Type*} [Category* C₀]
    [Category* C₁] [Category* C₂] {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₀₂ : C₀ ⥤ C₂}
    {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {G₂₀ : C₂ ⥤ C₀}
    (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁) (adj₀₂ : F₀₂ ⊣ G₂₀) (e : G₂₁ ⋙ G₁₀ ≅ G₂₀) :
    conjugateEquiv adj₀₂ (adj₀₁.comp adj₁₂)
      (Adjunction.leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e).hom = e.inv := by
  simp [Adjunction.leftAdjointCompIso_hom, Adjunction.leftAdjointCompNatTrans]

/-- Pasting tensor comparisons through coefficient squares: the comparison through the square
of `rE ≫ legE`, followed by the scalar normalization along `k ≫ cL = cE`, is the comparison
through `kh` and through the square of `rL ≫ legL`, combined by the scalar compositors. -/
theorem tensorThroughCoefficientSquare_paste
    {PE OE ME ML Λ V PL OL : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (pE : PE ≅ OE) (pL : PL ≅ OL) (t : Λ ≅ V)
    (rE : PE ⟶ ME) (rL : PL ⟶ ML) (cc : ME ⟶ ML) (legE : ME ⟶ Λ) (legL : ML ⟶ Λ)
    (hcoc : cc ≫ legL = legE) (kh : PE ⟶ PL) (hcs : kh ≫ rL = rE ≫ cc)
    (k : OE ⟶ OL) (cE : OE ⟶ V) (cL : OL ⟶ V) (hk : k ≫ cL = cE)
    (hθ : pE.hom ≫ k = kh ≫ pL.hom) (hmE : pE.hom ≫ cE = (rE ≫ legE) ≫ t.hom)
    (hmL : pL.hom ≫ cL = (rL ≫ legL) ≫ t.hom) (K) :
    (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction cc)
        (pbcDerivedScalarAdjunction legL) (pbcDerivedScalarAdjunction legE)
        (pbcDerivedRestrictComp cc legL legE hcoc)).inv.app
          ((pbcDerivedExtend rE).obj ((pbcDerivedRestrict pE.hom).obj K)) ≫
      (pbcDerivedExtend legL).map
        ((coefficientExtensionSquare X kh rL rE cc hcs).inv.app
            ((pbcDerivedRestrict pE.hom).obj K) ≫
          (pbcDerivedExtend rL).map ((tensorThroughCoefficientSquare X pE pL kh k hθ).inv.app K)) ≫
      (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction rL)
        (pbcDerivedScalarAdjunction legL) (pbcDerivedScalarAdjunction (rL ≫ legL))
        (pbcDerivedRestrictComp rL legL (rL ≫ legL) rfl)).hom.app
          ((pbcDerivedRestrict pL.hom).obj ((pbcDerivedExtend k).obj K)) ≫
      (tensorThroughCoefficientSquare X pL t (rL ≫ legL) cL hmL).inv.app
        ((pbcDerivedExtend k).obj K) =
    (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction rE)
        (pbcDerivedScalarAdjunction legE) (pbcDerivedScalarAdjunction (rE ≫ legE))
        (pbcDerivedRestrictComp rE legE (rE ≫ legE) rfl)).hom.app
          ((pbcDerivedRestrict pE.hom).obj K) ≫
      (tensorThroughCoefficientSquare X pE t (rE ≫ legE) cE hmE).inv.app K ≫
      (pbcDerivedRestrict t.hom).map
        ((Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction k)
          (pbcDerivedScalarAdjunction cL) (pbcDerivedScalarAdjunction cE)
          (pbcDerivedRestrictComp k cL cE hk)).inv.app K) := by
  let a {A B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}} (φ : A ⟶ B) :=
    pbcDerivedScalarAdjunction φ
  let j := Adjunction.leftAdjointCompIso (a cc) (a legL) (a legE)
    (pbcDerivedRestrictComp cc legL legE hcoc)
  let n := coefficientExtensionSquare X kh rL rE cc hcs
  let θ := tensorThroughCoefficientSquare X pE pL kh k hθ
  let xE := Adjunction.leftAdjointCompIso (a rE) (a legE) (a (rE ≫ legE))
    (pbcDerivedRestrictComp rE legE (rE ≫ legE) rfl)
  let xL := Adjunction.leftAdjointCompIso (a rL) (a legL) (a (rL ≫ legL))
    (pbcDerivedRestrictComp rL legL (rL ≫ legL) rfl)
  let mE := tensorThroughCoefficientSquare X pE t (rE ≫ legE) cE hmE
  let mL := tensorThroughCoefficientSquare X pL t (rL ≫ legL) cL hmL
  let N := Adjunction.leftAdjointCompIso (a k) (a cL) (a cE) (pbcDerivedRestrictComp k cL cE hk)
  let ψ : pbcDerivedExtend rE ⋙ pbcDerivedExtend legE ⟶
      pbcDerivedExtend kh ⋙ pbcDerivedExtend (rL ≫ legL) :=
    whiskerLeft (pbcDerivedExtend rE) j.inv ≫ (Functor.associator _ _ _).inv ≫
      whiskerRight n.inv (pbcDerivedExtend legL) ≫ (Functor.associator _ _ _).hom ≫
      whiskerLeft (pbcDerivedExtend kh) xL.hom
  let αL : TwoSquare (pbcDerivedRestrict pE.hom) (pbcDerivedExtend k ⋙ pbcDerivedExtend cL)
      (pbcDerivedExtend rE ⋙ pbcDerivedExtend legE) (pbcDerivedRestrict t.hom) :=
    (TwoSquare.vComp (TwoSquare.mk _ _ _ _ θ.inv) (TwoSquare.mk _ _ _ _ mL.inv)).whiskerRight ψ
  let αR : TwoSquare (pbcDerivedRestrict pE.hom) (pbcDerivedExtend k ⋙ pbcDerivedExtend cL)
      (pbcDerivedExtend rE ⋙ pbcDerivedExtend legE) (pbcDerivedRestrict t.hom) :=
    ((TwoSquare.mk _ _ _ _ mE.inv).whiskerRight xE.hom).whiskerLeft N.inv
  have hψ : conjugateEquiv ((a kh).comp (a (rL ≫ legL))) ((a rE).comp (a legE)) ψ =
      whiskerRight (pbcDerivedRestrictComp rL legL (rL ≫ legL) rfl).inv (pbcDerivedRestrict kh) ≫
        (Functor.associator _ _ _).hom ≫
        whiskerLeft (pbcDerivedRestrict legL) (derivedRestrictionSquare kh rL cc rE hcs).hom ≫
        (Functor.associator _ _ _).inv ≫
        whiskerRight (pbcDerivedRestrictComp cc legL legE hcoc).hom (pbcDerivedRestrict rE) := by
    have hα := congrArg Iso.inv (conjugateIsoEquiv_associator (a rE) (a cc) (a legL))
    simp only [conjugateIsoEquiv_apply_inv] at hα
    simp only [ψ, n]
    unfold coefficientExtensionSquare
    rw [← conjugateEquiv_comp _ ((a rE).comp ((a cc).comp (a legL))) _,
      ← conjugateEquiv_comp _ (((a rE).comp (a cc)).comp (a legL)) _,
      ← conjugateEquiv_comp _ (((a kh).comp (a rL)).comp (a legL)) _,
      ← conjugateEquiv_comp _ ((a kh).comp ((a rL).comp (a legL))) _,
      conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft,
      conjugateEquiv_associator_hom, hα, conjugateEquiv_leftAdjointCompIso_hom,
      Adjunction.conjugateEquiv_leftAdjointCompIso_inv,
      Adjunction.conjugateEquiv_leftAdjointCompIso_inv]
    simp only [Category.assoc]
  have key : αL = αR := by
    apply (mateEquiv ((a k).comp (a cL)) ((a rE).comp (a legE))).injective
    simp only [αL, αR]
    rw [mateEquiv_conjugateEquiv_vcomp _ ((a kh).comp (a (rL ≫ legL))), mateEquiv_hcomp,
      conjugateEquiv_mateEquiv_vcomp _ (a cE), mateEquiv_conjugateEquiv_vcomp _ (a (rE ≫ legE)),
      hψ, mateEquiv_tensorThroughCoefficientSquare_inv,
      mateEquiv_tensorThroughCoefficientSquare_inv, mateEquiv_tensorThroughCoefficientSquare_inv,
      conjugateEquiv_leftAdjointCompIso_hom, Adjunction.conjugateEquiv_leftAdjointCompIso_inv]
    ext Y
    simp only [comp_obj, TwoSquare.whiskerBottom_app, TwoSquare.hComp_app, NatTrans.comp_app,
      whiskerRight_app, associator_hom_app, whiskerLeft_app, associator_inv_app,
      Category.id_comp, Category.assoc, TwoSquare.whiskerTop_app, derivedRestrictionSquare,
      Iso.trans_hom, Iso.symm_hom, map_comp]
    exact restrictComp_paste pE.hom pL.hom t.hom rE rL cc legE legL hcoc kh hcs k cE cL hk hθ
      hmE hmL Y
  have hL := congrArg (fun α ↦ α.app K) key
  have hnat := xL.hom.naturality ((TwoSquare.mk _ _ _ _ θ.inv).app K)
  simp only [comp_obj, Functor.comp_map] at hnat
  simp only [αL, αR, ψ, TwoSquare.whiskerRight, TwoSquare.whiskerLeft, TwoSquare.vComp,
    NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, associator_hom_app,
    associator_inv_app, comp_obj, Category.id_comp, Category.comp_id, Category.assoc] at hL
  rw [← reassoc_of% hnat] at hL
  simpa only [map_comp, Category.assoc] using hL

/-- `tensorThroughCoefficientSquare_paste`, applied after a comparison which is the tensor
comparison through `kh` followed by a map `χ`, with the derived restrictions along `pE` and `pL`
given by any functors equal to them. -/
theorem tensorThroughCoefficientSquare_paste_heq
    {PE OE ME ML Λ V PL OL : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (pE : PE ≅ OE) (pL : PL ≅ OL) (t : Λ ≅ V)
    (rE : PE ⟶ ME) (rL : PL ⟶ ML) (cc : ME ⟶ ML) (legE : ME ⟶ Λ) (legL : ML ⟶ Λ)
    (hcoc : cc ≫ legL = legE) (kh : PE ⟶ PL) (hcs : kh ≫ rL = rE ≫ cc)
    (k : OE ⟶ OL) (cE : OE ⟶ V) (cL : OL ⟶ V) (hk : k ≫ cL = cE)
    (hθ : pE.hom ≫ k = kh ≫ pL.hom) (hmE : pE.hom ≫ cE = (rE ≫ legE) ≫ t.hom)
    (hmL : pL.hom ≫ cL = (rL ≫ legL) ≫ t.hom)
    (τE : DerivedCategory (pbcModules X OE) ⥤ DerivedCategory (pbcModules X PE))
    (hτE : τE = pbcDerivedRestrict pE.hom)
    (τL : DerivedCategory (pbcModules X OL) ⥤ DerivedCategory (pbcModules X PL))
    (hτL : τL = pbcDerivedRestrict pL.hom) (K TK) (χ : (pbcDerivedExtend k).obj K ⟶ TK)
    (c : (pbcDerivedExtend kh).obj (τE.obj K) ⟶ τL.obj TK)
    (hc : c ≍ (tensorThroughCoefficientSquare X pE pL kh k hθ).inv.app K ≫
      (pbcDerivedRestrict pL.hom).map χ) :
    ((Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction cc)
        (pbcDerivedScalarAdjunction legL) (pbcDerivedScalarAdjunction legE)
        (pbcDerivedRestrictComp cc legL legE hcoc)).inv.app
          ((pbcDerivedExtend rE).obj (τE.obj K)) ≫
      (pbcDerivedExtend legL).map
        ((coefficientExtensionSquare X kh rL rE cc hcs).inv.app (τE.obj K) ≫
          (pbcDerivedExtend rL).map c)) ≫
      (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction rL)
        (pbcDerivedScalarAdjunction legL) (pbcDerivedScalarAdjunction (rL ≫ legL))
        (pbcDerivedRestrictComp rL legL (rL ≫ legL) rfl)).hom.app (τL.obj TK) ≫
      (pbcDerivedExtend (rL ≫ legL)).map ((eqToHom hτL).app TK) ≫
      (tensorThroughCoefficientSquare X pL t (rL ≫ legL) cL hmL).inv.app TK ≍
    ((Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction rE)
        (pbcDerivedScalarAdjunction legE) (pbcDerivedScalarAdjunction (rE ≫ legE))
        (pbcDerivedRestrictComp rE legE (rE ≫ legE) rfl)).hom.app (τE.obj K) ≫
      (pbcDerivedExtend (rE ≫ legE)).map ((eqToHom hτE).app K) ≫
      (tensorThroughCoefficientSquare X pE t (rE ≫ legE) cE hmE).inv.app K) ≫
      (pbcDerivedRestrict t.hom).map
        ((pbcReductionNormalization k cL cE hk K).inv ≫ (pbcDerivedExtend cL).map χ) := by
  subst hτE hτL
  obtain rfl := eq_of_heq hc
  apply heq_of_eq
  have hN : (pbcReductionNormalization k cL cE hk K).inv =
      (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction k)
        (pbcDerivedScalarAdjunction cL) (pbcDerivedScalarAdjunction cE)
        (pbcDerivedRestrictComp k cL cE hk)).inv.app K := by
    rw [← Iso.app_inv]
    congr 1
    exact Iso.ext (pbcReductionNormalization_hom_eq k cL cE hk K)
  have hx := (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction rL)
    (pbcDerivedScalarAdjunction legL) (pbcDerivedScalarAdjunction (rL ≫ legL))
    (pbcDerivedRestrictComp rL legL (rL ≫ legL) rfl)).hom.naturality
      ((pbcDerivedRestrict pL.hom).map χ)
  have hm := (tensorThroughCoefficientSquare X pL t (rL ≫ legL) cL hmL).inv.naturality χ
  simp only [comp_obj, Functor.comp_map] at hx hm
  simp only [eqToHom_refl, NatTrans.id_app, map_id, Category.id_comp, map_comp,
    Category.assoc, hN]
  rw [reassoc_of% hx, hm]
  simpa only [map_comp, Category.assoc] using
    tensorThroughCoefficientSquare_paste pE pL t rE rL cc legE legL hcoc kh hcs k cE cL hk hθ
      hmE hmL K =≫ (pbcDerivedRestrict t.hom).map ((pbcDerivedExtend cL).map χ)

/-- `tensorThroughCoefficientSquare_paste_heq` as a tensor square, for isomorphisms given by
the transported tensor comparisons through the coefficient squares. -/
theorem integralTensorSquare_of_tensorThroughCoefficientSquare
    {PE OE ME ML Λ V PL OL : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (pE : PE ≅ OE) (pL : PL ≅ OL) (t : Λ ≅ V)
    (rE : PE ⟶ ME) (rL : PL ⟶ ML) (cc : ME ⟶ ML) (legE : ME ⟶ Λ) (legL : ML ⟶ Λ)
    (hcoc : cc ≫ legL = legE) (kh : PE ⟶ PL) (hcs : kh ≫ rL = rE ≫ cc)
    (k : OE ⟶ OL) (cE : OE ⟶ V) (cL : OL ⟶ V) (hk : k ≫ cL = cE)
    (hθ : pE.hom ≫ k = kh ≫ pL.hom) (hmE : pE.hom ≫ cE = (rE ≫ legE) ≫ t.hom)
    (hmL : pL.hom ≫ cL = (rL ≫ legL) ≫ t.hom)
    (τE : DerivedCategory (pbcModules X OE) ⥤ DerivedCategory (pbcModules X PE))
    (hτE : τE = pbcDerivedRestrict pE.hom)
    (τL : DerivedCategory (pbcModules X OL) ⥤ DerivedCategory (pbcModules X PL))
    (hτL : τL = pbcDerivedRestrict pL.hom)
    {𝒞E 𝒞L : Type*} [Category* 𝒞E] [Category* 𝒞L]
    (IE : 𝒞E ⥤ DerivedCategory (pbcModules X OE)) (IL : 𝒞L ⥤ DerivedCategory (pbcModules X OL))
    (KE : 𝒞E) (KL : 𝒞L) (χ : (pbcDerivedExtend k).obj (IE.obj KE) ⟶ IL.obj KL)
    (c : (pbcDerivedExtend kh).obj (τE.obj (IE.obj KE)) ⟶ τL.obj (IL.obj KL))
    (hc : c ≍ (tensorThroughCoefficientSquare X pE pL kh k hθ).inv.app (IE.obj KE) ≫
      (pbcDerivedRestrict pL.hom).map χ)
    (f : (pbcDerivedExtend legE).obj ((pbcDerivedExtend rE).obj (τE.obj (IE.obj KE))) ⟶
      (pbcDerivedExtend legL).obj ((pbcDerivedExtend rL).obj (τL.obj (IL.obj KL))))
    (hf : f = (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction cc)
        (pbcDerivedScalarAdjunction legL) (pbcDerivedScalarAdjunction legE)
        (pbcDerivedRestrictComp cc legL legE hcoc)).inv.app
          ((pbcDerivedExtend rE).obj (τE.obj (IE.obj KE))) ≫
      (pbcDerivedExtend legL).map
        ((coefficientExtensionSquare X kh rL rE cc hcs).inv.app (τE.obj (IE.obj KE)) ≫
          (pbcDerivedExtend rL).map c))
    (mE : IE ⋙ τE ⋙ pbcDerivedExtend rE ⋙ pbcDerivedExtend legE ≅
      IE ⋙ pbcDerivedExtend cE ⋙ pbcDerivedRestrict t.hom)
    (hmE' : mE = isoWhiskerLeft (IE ⋙ τE)
      (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction rE)
        (pbcDerivedScalarAdjunction legE) (pbcDerivedScalarAdjunction (rE ≫ legE))
        (pbcDerivedRestrictComp rE legE (rE ≫ legE) rfl)) ≪≫
      isoWhiskerRight (isoWhiskerLeft IE (eqToIso hτE)) (pbcDerivedExtend (rE ≫ legE)) ≪≫
      isoWhiskerLeft IE (tensorThroughCoefficientSquare X pE t (rE ≫ legE) cE hmE).symm)
    (mL : IL ⋙ τL ⋙ pbcDerivedExtend rL ⋙ pbcDerivedExtend legL ≅
      IL ⋙ pbcDerivedExtend cL ⋙ pbcDerivedRestrict t.hom)
    (hmL' : mL = isoWhiskerLeft (IL ⋙ τL)
      (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction rL)
        (pbcDerivedScalarAdjunction legL) (pbcDerivedScalarAdjunction (rL ≫ legL))
        (pbcDerivedRestrictComp rL legL (rL ≫ legL) rfl)) ≪≫
      isoWhiskerRight (isoWhiskerLeft IL (eqToIso hτL)) (pbcDerivedExtend (rL ≫ legL)) ≪≫
      isoWhiskerLeft IL (tensorThroughCoefficientSquare X pL t (rL ≫ legL) cL hmL).symm) :
    integralTensorSquare f (mE.app KE) (mL.app KL)
      ((pbcDerivedRestrict t.hom).map
        ((pbcReductionNormalization k cL cE hk (IE.obj KE)).inv ≫
          (pbcDerivedExtend cL).map χ)) := by
  subst hf hmE' hmL'
  unfold integralTensorSquare
  simpa only [Iso.app_hom, isoWhiskerLeft_hom, whiskerLeft_app, Iso.trans_hom,
    NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app, Iso.symm_hom, Category.assoc,
    comp_obj, map_comp, eqToIso.hom] using
    tensorThroughCoefficientSquare_paste_heq pE pL t rE rL cc legE legL hcoc kh hcs k cE cL hk hθ
      hmE hmL τE hτE τL hτL (IE.obj KE) (IL.obj KL) χ c hc

/-- On a complex, the inverse tensor comparison through a coefficient square, followed by the
scalar-extension counit, is the counit of the other extension followed by an ordinary comparison
whose transpose is the ordinary restriction square. -/
@[reassoc]
theorem tensorThroughCoefficientSquare_inv_app_Q
    {R P V T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (d : R ≅ P) (q : V ≅ T) (s : R ⟶ V) (c : P ⟶ T) (h : d.hom ≫ c = s ≫ q.hom)
    (o : pbcRestrict d.hom ⋙ pbcExtend s ⟶ pbcExtend c ⋙ pbcRestrict q.hom)
    (ho : ∀ M, (pbcScalarAdjunction s).unit.app ((pbcRestrict d.hom).obj M) ≫
        (pbcRestrict s).map (o.app M) =
      (pbcRestrict d.hom).map ((pbcScalarAdjunction c).unit.app M) ≫
        (pbcRestrictComp d.hom c (d.hom ≫ c) rfl).hom.app ((pbcExtend c).obj M) ≫
        (pbcRestrictComp s q.hom (d.hom ≫ c) h.symm).inv.app ((pbcExtend c).obj M))
    (K : CochainComplex (pbcModules X P) ℤ) :
    (tensorThroughCoefficientSquare X d q s c h).inv.app (DerivedCategory.Q.obj K) ≫
        (pbcDerivedRestrict q.hom).map (pbcComplexCounit c K) ≫
        (pbcRestrict q.hom).mapDerivedCategoryFactors.hom.app
          (((pbcExtend c).mapHomologicalComplex (.up ℤ)).obj K) =
      (pbcDerivedExtend s).map ((pbcRestrict d.hom).mapDerivedCategoryFactors.hom.app K) ≫
        pbcComplexCounit s (((pbcRestrict d.hom).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex o (.up ℤ)).app K) := by
  let N := ((pbcExtend c).mapHomologicalComplex (.up ℤ)).obj K
  let K' := ((pbcRestrict d.hom).mapHomologicalComplex (.up ℤ)).obj K
  apply ((pbcDerivedScalarAdjunction s).homEquiv _ _).injective
  apply (cancel_mono ((pbcRestrict s).mapDerivedCategoryFactors.hom.app
    (((pbcRestrict q.hom).mapHomologicalComplex (.up ℤ)).obj N))).1
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
  -- the left side, through the mate of the tensor comparison
  have hm := unit_mateEquiv (pbcDerivedScalarAdjunction c)
    (pbcDerivedScalarAdjunction s) (tensorThroughCoefficientSquare X d q s c h).inv
    (DerivedCategory.Q.obj K)
  rw [mateEquiv_tensorThroughCoefficientSquare_inv] at hm
  rw [← reassoc_of% hm]
  have hρ := (derivedRestrictionSquare d.hom c q.hom s h).hom.naturality (pbcComplexCounit c K)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hρ
  erw [← reassoc_of% hρ]
  have hR : (derivedRestrictionSquare d.hom c q.hom s h).hom.app (DerivedCategory.Q.obj N) ≫
      (pbcDerivedRestrict s).map ((pbcRestrict q.hom).mapDerivedCategoryFactors.hom.app N) ≫
      (pbcRestrict s).mapDerivedCategoryFactors.hom.app
        (((pbcRestrict q.hom).mapHomologicalComplex (.up ℤ)).obj N) =
      (pbcDerivedRestrict d.hom).map ((pbcRestrict c).mapDerivedCategoryFactors.hom.app N) ≫
        (pbcRestrict d.hom).mapDerivedCategoryFactors.hom.app
          (((pbcRestrict c).mapHomologicalComplex (.up ℤ)).obj N) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          ((pbcRestrictComp d.hom c (d.hom ≫ c) rfl).hom ≫
            (pbcRestrictComp s q.hom (d.hom ≫ c) h.symm).inv) (.up ℤ)).app N) := by
    have h1 := pbcDerivedRestrictComp_hom_app_Q d.hom c (d.hom ≫ c) rfl N
    have h2 := pbcDerivedRestrictComp_hom_app_Q s q.hom (d.hom ≫ c) h.symm N
    have h2' : (pbcDerivedRestrictComp s q.hom (d.hom ≫ c) h.symm).inv.app
        (DerivedCategory.Q.obj N) ≫
        (pbcDerivedRestrict s).map ((pbcRestrict q.hom).mapDerivedCategoryFactors.hom.app N) ≫
        (pbcRestrict s).mapDerivedCategoryFactors.hom.app
          (((pbcRestrict q.hom).mapHomologicalComplex (.up ℤ)).obj N) =
        (pbcRestrict (d.hom ≫ c)).mapDerivedCategoryFactors.hom.app N ≫
          DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
            (pbcRestrictComp s q.hom (d.hom ≫ c) h.symm).inv (.up ℤ)).app N) := by
      rw [← cancel_epi ((pbcDerivedRestrictComp s q.hom (d.hom ≫ c) h.symm).hom.app
        (DerivedCategory.Q.obj N)), Iso.hom_inv_id_app_assoc, reassoc_of% h2,
        ← DerivedCategory.Q.map_comp, ← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp,
        Iso.hom_inv_id, NatTrans.mapHomologicalComplex_id]
      erw [DerivedCategory.Q.map_id, Category.comp_id]
    simp only [derivedRestrictionSquare, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Category.assoc]
    rw [h2', reassoc_of% h1, NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app,
      DerivedCategory.Q.map_comp]
  erw [hR]
  have hc := congrArg (pbcDerivedRestrict d.hom).map (pbcDerivedScalarAdjunction_unit_app_Q c K)
  simp only [Functor.map_comp] at hc
  erw [reassoc_of% hc]
  have hd := (pbcRestrict d.hom).mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex (pbcScalarAdjunction c).unit (.up ℤ)).app K)
  erw [reassoc_of% hd]
  have hu := (pbcDerivedScalarAdjunction s).unit.naturality
    ((pbcRestrict d.hom).mapDerivedCategoryFactors.hom.app K)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at hu
  erw [← reassoc_of% hu]
  have hf := (pbcRestrict s).mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex o (.up ℤ)).app K)
  erw [hf]
  erw [reassoc_of% (pbcDerivedScalarAdjunction_unit_app_Q s K')]
  dsimp only [Functor.comp_map]
  erw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  congr 2
  apply HomologicalComplex.hom_ext
  intro n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, NatTrans.comp_app]
  exact (ho (K.X n)).symm

/-- The inverse tensor comparison through a coefficient square on a complex, for an ordinary
comparison fixed on the unit tensor generators. -/
@[reassoc]
theorem tensorThroughCoefficientSquare_inv_app_Q_of_tensorSection
    {R P V T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (d : R ≅ P) (q : V ≅ T) (s : R ⟶ V) (c : P ⟶ T) (h : d.hom ≫ c = s ≫ q.hom)
    (o : pbcExtend c ⋙ pbcRestrict q.hom ≅ pbcRestrict d.hom ⋙ pbcExtend s)
    (ho : ∀ (M : pbcModules X P) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
      (o.hom.app M).val.app U (pbcTensorSection c M U 1 x) =
        pbcTensorSection s ((pbcRestrict d.hom).obj M) U 1 x)
    (K : CochainComplex (pbcModules X P) ℤ) :
    (tensorThroughCoefficientSquare X d q s c h).inv.app (DerivedCategory.Q.obj K) ≫
        (pbcDerivedRestrict q.hom).map (pbcComplexCounit c K) ≫
        (pbcRestrict q.hom).mapDerivedCategoryFactors.hom.app
          (((pbcExtend c).mapHomologicalComplex (.up ℤ)).obj K) =
      (pbcDerivedExtend s).map ((pbcRestrict d.hom).mapDerivedCategoryFactors.hom.app K) ≫
        pbcComplexCounit s (((pbcRestrict d.hom).mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex o.inv (.up ℤ)).app K) := by
  refine tensorThroughCoefficientSquare_inv_app_Q d q s c h o.inv (fun M ↦ ?_) K
  refine (cancel_mono ((pbcRestrict s).map (o.hom.app M))).1 ?_
  rw [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  ext U x
  have hinv (N : pbcModules X T) (y : N.val.obj U) :
      ((pbcRestrictComp s q.hom (d.hom ≫ c) h.symm).inv.app N).val.app U y = y := by
    have h1 := (pbcRestrictComp_exists s q.hom (d.hom ≫ c) h.symm).exists.choose_spec N U
      (((pbcRestrictComp s q.hom (d.hom ≫ c) h.symm).inv.app N).val.app U y)
    exact h1.symm.trans (congrArg (fun k ↦ k.val.app U y)
      ((pbcRestrictComp s q.hom (d.hom ≫ c) h.symm).inv_hom_id_app N))
  change ((pbcScalarAdjunction s).unit.app ((pbcRestrict d.hom).obj M)).val.app U x =
    (o.hom.app M).val.app U (((pbcRestrictComp s q.hom (d.hom ≫ c) h.symm).inv.app _).val.app U
      (((pbcRestrictComp d.hom c (d.hom ≫ c) rfl).hom.app _).val.app U
        (((pbcScalarAdjunction c).unit.app M).val.app U x)))
  rw [hinv]
  refine ((pbcScalarAdjunction_exists s).exists.choose_spec _ U x).trans ?_
  refine (ho M U x).symm.trans ?_
  congr 1
  exact (((pbcRestrictComp_exists d.hom c _ rfl).exists.choose_spec _ U _).trans
    ((pbcScalarAdjunction_exists c).exists.choose_spec M U x)).symm

end AlgebraicGeometry.Scheme
