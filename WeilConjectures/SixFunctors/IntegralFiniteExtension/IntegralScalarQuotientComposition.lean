/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionCore
import all WeilConjectures.AlgebraicGeometry.Completed.Pullback.CompletedPullbackReductionCoherence

/-! # Composition of the normalized finite scalar reduction squares

Source: lem-coef-integral-finite-extension.proof.md, first and final paragraphs.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

private local instance derived (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    HasDerivedCategory.{u + 2} (pbcModules X R) := HasDerivedCategory.standard _

private theorem tensorComposition_eq {X : Scheme.{u}}
    {R S T : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (d : R ⟶ T) (h : a ≫ b = d) :
    PurCompactSupport.tensorComposition a b d h =
      Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction a)
        (pbcDerivedScalarAdjunction b) (pbcDerivedScalarAdjunction d)
        (pbcDerivedRestrictComp a b d h) := by
  apply Iso.ext
  ext K
  simp [PurCompactSupport.tensorComposition, Adjunction.leftAdjointCompIso,
    Adjunction.leftAdjointUniq]

private theorem tensorComposition_assoc {X : Scheme.{u}}
    {R S T V : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (c : T ⟶ V)
    (ab : R ⟶ T) (bc : S ⟶ V) (abc : R ⟶ V)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (habc : a ≫ bc = abc) (hab_c : ab ≫ c = abc)
    (K : DerivedCategory.{u + 2} (pbcModules X R)) :
    (pbcDerivedExtend c).map ((PurCompactSupport.tensorComposition a b ab hab).hom.app K) ≫
        (PurCompactSupport.tensorComposition ab c abc hab_c).hom.app K =
      (PurCompactSupport.tensorComposition b c bc hbc).hom.app ((pbcDerivedExtend a).obj K) ≫
        (PurCompactSupport.tensorComposition a bc abc habc).hom.app K := by
  simpa only [AlgebraicGeometry.Scheme.norm_eq, tensorComposition_eq] using
    AlgebraicGeometry.Scheme.norm_assoc a b c ab bc abc hab hbc habc hab_c K

private theorem tensorSquare_composition {X : Scheme.{u}}
    {R S T R' S' T' : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ T) (ab : R ⟶ T)
    (a' : R' ⟶ S') (b' : S' ⟶ T') (ab' : R' ⟶ T')
    (r : R ⟶ R') (s : S ⟶ S') (t : T ⟶ T')
    (hab : a ≫ b = ab) (hab' : a' ≫ b' = ab')
    (ha : a ≫ s = r ≫ a') (hb : b ≫ t = s ≫ b')
    (hc : ab ≫ t = r ≫ ab') (K : DerivedCategory.{u + 2} (pbcModules X R)) :
    (pbcDerivedExtend t).map ((PurCompactSupport.tensorComposition a b ab hab).hom.app K) ≫
        (PurCompactSupport.tensorSquare ab ab' r t hc).hom.app K =
      (PurCompactSupport.tensorSquare b b' s t hb).hom.app ((pbcDerivedExtend a).obj K) ≫
        (pbcDerivedExtend b').map ((PurCompactSupport.tensorSquare a a' r s ha).hom.app K) ≫
        (PurCompactSupport.tensorComposition a' b' ab' hab').hom.app
          ((pbcDerivedExtend r).obj K) := by
  have h1 := tensorComposition_assoc a b t ab (b ≫ t) (ab ≫ t)
    hab rfl (by rw [← Category.assoc, hab]) rfl K
  have h2 := tensorComposition_assoc a s b' (a ≫ s) (b ≫ t) (ab ≫ t)
    rfl hb.symm (by rw [← Category.assoc, hab])
    (by rw [Category.assoc, ← hb, ← Category.assoc, hab]) K
  have h3 := tensorComposition_assoc r a' b' (a ≫ s) ab' (ab ≫ t)
    ha.symm hab' hc.symm
    (by rw [ha, Category.assoc, hab', ← hc]) K
  dsimp only [PurCompactSupport.tensorSquare, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc, h1, Category.assoc]
  congr 1
  apply (cancel_epi
    ((PurCompactSupport.tensorComposition s b' (b ≫ t) hb.symm).hom.app
      ((pbcDerivedExtend a).obj K))).1
  simp only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  simp only [Category.assoc]
  rw [← reassoc_of% h2]
  congr 1
  apply (cancel_epi ((pbcDerivedExtend b').map
    ((PurCompactSupport.tensorComposition r a' (a ≫ s) ha.symm).hom.app K))).1
  simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app]
  rw [h3]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  rw [(pbcDerivedExtend b').map_id]
  simp only [Category.id_comp]
  exact Category.comp_id _

private theorem conjugate_square
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    (P : A ⥤ B) (Q : B ⥤ C) (J : A ⥤ C)
    (P' : D ⥤ E) (Q' : E ⥤ F) (J' : D ⥤ F)
    (r r' : A ⥤ D) (s s' : B ⥤ E) (t t' : C ⥤ F)
    (er : r ≅ r') (es : s ≅ s') (et : t ≅ t')
    (α : P ⋙ Q ≅ J) (β : P' ⋙ Q' ≅ J')
    (x : P ⋙ s ≅ r ⋙ P') (y : Q ⋙ t ≅ s ⋙ Q')
    (z : J ⋙ t ≅ r ⋙ J') (K : A)
    (h : t.map (α.hom.app K) ≫ z.hom.app K =
      y.hom.app (P.obj K) ≫ Q'.map (x.hom.app K) ≫ β.hom.app (r.obj K)) :
    t'.map (α.hom.app K) ≫
        (et.inv.app (J.obj K) ≫ z.hom.app K ≫ J'.map (er.hom.app K)) =
      (et.inv.app (Q.obj (P.obj K)) ≫ y.hom.app (P.obj K) ≫
          Q'.map (es.hom.app (P.obj K))) ≫
        Q'.map (es.inv.app (P.obj K) ≫ x.hom.app K ≫ P'.map (er.hom.app K)) ≫
        β.hom.app (r'.obj K) := by
  simp only [Functor.map_comp, Category.assoc]
  rw [et.inv.naturality_assoc, reassoc_of% h]
  rw [← Q'.map_comp_assoc (es.hom.app (P.obj K)) (es.inv.app (P.obj K)),
    Iso.hom_inv_id_app, Q'.map_id, Category.id_comp]
  rw [← β.hom.naturality (er.hom.app K)]
  rfl

private theorem completion_square
    {A B C D E F : Type*} [Category A] [Category B] [Category C]
    [Category D] [Category E] [Category F]
    (P : A ⥤ B) (Q : B ⥤ C) (J : A ⥤ C)
    (P' : D ⥤ E) (Q' : E ⥤ F) (J' : D ⥤ F)
    (r : A ⥤ D) (s : B ⥤ E) (t : C ⥤ F)
    (α : P ⋙ Q ≅ J) (β : P' ⋙ Q' ≅ J')
    (x : P ⋙ s ≅ r ⋙ P') (y : Q ⋙ t ≅ s ⋙ Q')
    (z : J ⋙ t ≅ r ⋙ J') (K : A)
    (h : t.map (α.hom.app K) ≫ z.hom.app K =
      y.hom.app (P.obj K) ≫ Q'.map (x.hom.app K) ≫ β.hom.app (r.obj K))
    {TK : B} {UTK JK : C}
    (cK : P.obj K ≅ TK) (cU : Q.obj TK ≅ UTK) (cJ : J.obj K ≅ JK) :
    t.map ((cU.symm ≪≫ Q.mapIso cK.symm ≪≫ α.app K ≪≫ cJ).hom) ≫
        (t.map cJ.inv ≫ z.hom.app K) =
      (t.map cU.inv ≫ y.hom.app TK) ≫
        Q'.map (s.map cK.inv ≫ x.hom.app K) ≫ β.hom.app (r.obj K) := by
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [← t.map_comp_assoc cJ.hom cJ.inv, Iso.hom_inv_id, t.map_id, Category.id_comp]
  rw [h]
  have hn := y.hom.naturality cK.inv
  dsimp only [Functor.comp_map] at hn
  rw [reassoc_of% hn]

/-- Pasting two scalar/reduction squares gives the square for the composite,
with the actual completed and finite scalar associators. There are no dualizing
or internal-Hom comparison maps in this assertion.
Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-integral-finite-extension.proof.md, first and final paragraphs.
(blueprint: lem-sf-integral-scalar-quotient-composition)

Proof: expand quotient into reduction of inverse completion, inverse normalized
finiteReductionIso, tensorSquare, and scalar extension of finiteReductionIso.
Expand comp into inverse completion for the second inclusion, extension of inverse
completion for the first, the ordinary scalar associator, and completion for the
composite. Naturality moves each completion map through reduction and tensorSquare;
adjacent inverse pairs cancel. The remaining equation is the pasting law for
ordinary scalar associators and the two quotient squares. All these isomorphisms
are mates of the section-normalized restriction composition maps. The two pasted
restriction maps coincide, hence uniqueness of mates gives the required equation.
Equivalently both maps send the class of t tensor (s tensor x) to the class of ts
tensor x on flat-term K-flat representatives. Localization preserves this equation.
The proof requires only completeness of K and applies also to zero objects, empty
schemes, identity inclusions and the exponent-one reduction. -/
theorem quotient_scalar_composition
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (j : L →ₐ[Padic l] F) (n : ℕ)
    (h : integralScalarQuotientSheafMap l E L ι X n ≫
      integralScalarQuotientSheafMap l L F j X n =
        integralScalarQuotientSheafMap l E F (j.comp ι) X n)
    (K : IntegralVerdier.Ambient l E X) (hK : IsSfDerivedComplete l E X K) :
    (scalarReductionDerivedExtension l F X n).map
        (comp l E L ι X F j K hK).hom ≫
      (quotient l E F (j.comp ι) X n K hK).hom =
    (quotient l L F j X n
      ((integralScalarExtensionOfUniverses l E L ι X).obj K)
      (extension_complete l E L ι X K hK)).hom ≫
      (pbcDerivedExtend (integralScalarQuotientSheafMap l L F j X n)).map
        (quotient l E L ι X n K hK).hom ≫
      (PurCompactSupport.tensorComposition
        (integralScalarQuotientSheafMap l E L ι X n)
        (integralScalarQuotientSheafMap l L F j X n)
        (integralScalarQuotientSheafMap l E F (j.comp ι) X n) h).hom.app
          ((scalarReductionDerivedExtension l E X n).obj K) := by
  let ai := completedCoefficientMap l E L ι X
  let aj := completedCoefficientMap l L F j X
  let aij := completedCoefficientMap l E F (j.comp ι) X
  let bi := integralScalarQuotientSheafMap l E L ι X n
  let bj := integralScalarQuotientSheafMap l L F j X n
  let bij := integralScalarQuotientSheafMap l E F (j.comp ι) X n
  let rE := completedIntegralCommRingProjectionUnrestricted l E X n
  let rL := completedIntegralCommRingProjectionUnrestricted l L X n
  let rF := completedIntegralCommRingProjectionUnrestricted l F X n
  let P := pbcDerivedExtend ai
  let Q := pbcDerivedExtend aj
  let J := pbcDerivedExtend aij
  let P' := pbcDerivedExtend bi
  let Q' := pbcDerivedExtend bj
  let J' := pbcDerivedExtend bij
  let RE := scalarReductionDerivedExtension l E X n
  let RL := scalarReductionDerivedExtension l L X n
  let RF := scalarReductionDerivedExtension l F X n
  let eE := PurCompactSupport.finiteReductionIso l E X n
  let eL := PurCompactSupport.finiteReductionIso l L X n
  let eF := PurCompactSupport.finiteReductionIso l F X n
  let hi := (completedCoefficientMap_existsUnique l E L ι X).exists.choose_spec n
  let hj := (completedCoefficientMap_existsUnique l L F j X).exists.choose_spec n
  let hij := (completedCoefficientMap_existsUnique l E F (j.comp ι) X).exists.choose_spec n
  let ha := PurCompactSupport.completedMap_composition l E L ι F j X
  let α := PurCompactSupport.tensorComposition ai aj aij ha
  let β := PurCompactSupport.tensorComposition bi bj bij h
  let si := PurCompactSupport.tensorSquare ai bi rE rL hi
  let sj := PurCompactSupport.tensorSquare aj bj rL rF hj
  let sij := PurCompactSupport.tensorSquare aij bij rE rF hij
  let xi : P ⋙ RL ≅ RE ⋙ P' :=
    Functor.isoWhiskerLeft P eL.symm ≪≫ si ≪≫ Functor.isoWhiskerRight eE P'
  let xj : Q ⋙ RF ≅ RL ⋙ Q' :=
    Functor.isoWhiskerLeft Q eF.symm ≪≫ sj ≪≫ Functor.isoWhiskerRight eL Q'
  let xij : J ⋙ RF ≅ RE ⋙ J' :=
    Functor.isoWhiskerLeft J eF.symm ≪≫ sij ≪≫ Functor.isoWhiskerRight eE J'
  have hs := tensorSquare_composition ai aj aij bi bj bij rE rL rF ha h hi hj hij K
  have hc := conjugate_square P Q J P' Q' J'
    (pbcDerivedExtend rE) RE (pbcDerivedExtend rL) RL (pbcDerivedExtend rF) RF
    eE eL eF α β si sj sij K hs
  have ht : RF.map (α.hom.app K) ≫ xij.hom.app K =
      xj.hom.app (P.obj K) ≫ Q'.map (xi.hom.app K) ≫ β.hom.app (RE.obj K) := hc
  exact completion_square P Q J P' Q' J' RE RL RF α β xi xj xij K ht
    (completion l E L ι X K hK)
    (completion l L F j X _ (extension_complete l E L ι X K hK))
    (completion l E F (j.comp ι) X K hK)

end WeilConjectures.IntegralFiniteExtension
