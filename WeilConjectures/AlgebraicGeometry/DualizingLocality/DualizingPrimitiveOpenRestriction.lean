/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleNormalization.FiniteEtaleDualizingNormalization
import all WeilConjectures.SmoothPurity.PurityFiniteSetting.DualizingUnitComposite
import WeilConjectures.AlgebraicGeometry.SmoothExceptionalPasting.SmoothExceptionalTensorPasting
import WeilConjectures.AlgebraicGeometry.DualizingLocality.DualizingCocycleSourceEtale
import all WeilConjectures.AlgebraicGeometry.Section.SectionExceptionalFibreCoherence
import WeilConjectures.EtaleCohomology.Purity.Smooth.SectionInvariantCtf
import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual

/-! # Primitive dualizing maps under compatible open restrictions

Source: thm-pur-composition-coherence, proof Step 1, and the indicated steps
of lem-pur-dualizing-sigma-cocycle-locality. The statement expands the existing
locality predicates to keep this proof dependency independent of its consumer.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.DualizingLocality
open FiniteEtaleNormalization

attribute [local instance high] SymmetricCategory.toBraidedCategory

private theorem conjugate_composition_assoc
    {C₀ C₁ C₂ C₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    {F : C₀ ⥤ C₁} {G : C₁ ⥤ C₂} {H : C₂ ⥤ C₃}
    {FG : C₀ ⥤ C₂} {GH : C₁ ⥤ C₃} {FGH : C₀ ⥤ C₃}
    {RF : C₁ ⥤ C₀} {RG : C₂ ⥤ C₁} {RH : C₃ ⥤ C₂}
    {RFG : C₂ ⥤ C₀} {RGH : C₃ ⥤ C₁} {RFGH : C₃ ⥤ C₀}
    (af : F ⊣ RF) (ag : G ⊣ RG) (ah : H ⊣ RH)
    (afg : FG ⊣ RFG) (agh : GH ⊣ RGH) (afgh : FGH ⊣ RFGH)
    (ab : F ⋙ G ≅ FG) (bc : G ⋙ H ≅ GH)
    (abc : F ⋙ GH ≅ FGH) (abc' : FG ⋙ H ≅ FGH)
    (h : Functor.whiskerLeft F bc.hom ≫ abc.hom =
      (Functor.associator F G H).inv ≫ Functor.whiskerRight ab.hom H ≫ abc'.hom) :
    (conjugateIsoEquiv afgh (af.comp agh) abc).hom ≫
        Functor.whiskerRight (conjugateIsoEquiv agh (ag.comp ah) bc).hom RF =
      (conjugateIsoEquiv afgh (afg.comp ah) abc').hom ≫
        Functor.whiskerLeft RH (conjugateIsoEquiv afg (af.comp ag) ab).hom := by
  let t₁ := (conjugateIsoEquiv afg (af.comp ag) ab).hom
  let t₂ := (conjugateIsoEquiv agh (ag.comp ah) bc).hom
  let t₃ := (conjugateIsoEquiv afgh (af.comp agh) abc).hom
  let t₄ := (conjugateIsoEquiv afgh (afg.comp ah) abc').hom
  have hab : Adjunction.leftAdjointCompNatTrans af ag afg t₁ = ab.hom := by
    simp [Adjunction.leftAdjointCompNatTrans, t₁, conjugateIsoEquiv_apply_hom]
  have hbc : Adjunction.leftAdjointCompNatTrans ag ah agh t₂ = bc.hom := by
    simp [Adjunction.leftAdjointCompNatTrans, t₂, conjugateIsoEquiv_apply_hom]
  have habc : Adjunction.leftAdjointCompNatTrans af agh afgh t₃ = abc.hom := by
    simp [Adjunction.leftAdjointCompNatTrans, t₃, conjugateIsoEquiv_apply_hom]
  have habc' : Adjunction.leftAdjointCompNatTrans afg ah afgh t₄ = abc'.hom := by
    simp [Adjunction.leftAdjointCompNatTrans, t₄, conjugateIsoEquiv_apply_hom]
  rw [← hab, ← hbc, ← habc, ← habc'] at h
  rw [Adjunction.leftAdjointCompNatTrans₀₁₃_eq_conjugateEquiv_symm,
    Adjunction.leftAdjointCompNatTrans₀₂₃_eq_conjugateEquiv_symm] at h
  have ht := (conjugateEquiv afgh (af.comp (ag.comp ah))).symm.injective h
  apply NatTrans.ext
  funext K
  simpa only [NatTrans.comp_app, Functor.associator_inv_app, Category.comp_id]
    using congr_app ht K

private theorem fieldSchemeNoetherian
    (P : WeilConjectures.PurityFiniteSetting.{u})
    (X : Scheme.{u}) [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))] : IsNoetherian X :=
  { toIsLocallyNoetherian :=
      LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (.of P.field.k))
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of P.field.k)) }

private def exceptionalCompEq
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (fg : X ⟶ Z) [fg.IsOver (Spec (.of P.field.k))]
    [IsSeparated fg] [LocallyOfFiniteType fg] [QuasiCompact fg]
    (w : f ≫ g = fg) :
    exceptional P fg ≅ exceptional P g ⋙ exceptional P f :=
  FiniteEtaleNormalization.congr P fg (f ≫ g) w.symm ≪≫ comp P f g

private theorem exceptionalCompEq_conjugate
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (fg : X ⟶ Z) [fg.IsOver (Spec (.of P.field.k))]
    [IsSeparated fg] [LocallyOfFiniteType fg] [QuasiCompact fg]
    (w : f ≫ g = fg) :
    exceptionalCompEq P f g fg w =
      let := compactification P f
      let := compactification P g
      let := compactification P fg
      let := compactification P (f ≫ g)
      conjugateIsoEquiv (Etale.rightDerivedUpperShriekAdjunction P.Coefficient fg)
        ((Etale.rightDerivedUpperShriekAdjunction P.Coefficient f).comp
          (Etale.rightDerivedUpperShriekAdjunction P.Coefficient g))
        (Etale.unboundedEtaleLowerShriekCompIso P.Coefficient f g ≪≫
          Etale.unboundedEtaleLowerShriekCongr P.Coefficient w) := by
  subst fg
  apply Iso.ext
  ext K
  simp [exceptionalCompEq, FiniteEtaleNormalization.congr,
    Etale.unboundedEtaleLowerShriekCongr, comp, conjugateIsoEquiv_apply_hom]

private theorem exceptionalCompEq_assoc
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {W X Y Z : Scheme.{u}}
    [W.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of P.field.k))]
    [QuasiCompact (W ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (a : W ⟶ X) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (b : X ⟶ Y) [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (c : Y ⟶ Z) [c.IsOver (Spec (.of P.field.k))]
    [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
    (ab : W ⟶ Y) [ab.IsOver (Spec (.of P.field.k))]
    [IsSeparated ab] [LocallyOfFiniteType ab] [QuasiCompact ab]
    (bc : X ⟶ Z) [bc.IsOver (Spec (.of P.field.k))]
    [IsSeparated bc] [LocallyOfFiniteType bc] [QuasiCompact bc]
    (abc : W ⟶ Z) [abc.IsOver (Spec (.of P.field.k))]
    [IsSeparated abc] [LocallyOfFiniteType abc] [QuasiCompact abc]
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (hl : ab ≫ c = abc) (hr : a ≫ bc = abc)
    (K : Etale.DerivedCategoryModule P.Coefficient Z) :
    (exceptionalCompEq P a bc abc hr).hom.app K ≫
        (exceptional P a).map ((exceptionalCompEq P b c bc hbc).hom.app K) =
      (exceptionalCompEq P ab c abc hl).hom.app K ≫
        (exceptionalCompEq P a b ab hab).hom.app ((exceptional P c).obj K) := by
  subst ab bc
  cases hr
  let := fieldSchemeNoetherian P W
  let := fieldSchemeNoetherian P X
  let := fieldSchemeNoetherian P Y
  let := fieldSchemeNoetherian P Z
  let := compactification P a
  let := compactification P b
  let := compactification P c
  let := compactification P (a ≫ b)
  let := compactification P (b ≫ c)
  let := compactification P ((a ≫ b) ≫ c)
  let := compactification P (a ≫ b ≫ c)
  have ha := Etale.unboundedEtaleLowerShriekCompIso_assoc P.Coefficient a b c
  let cab := Etale.unboundedEtaleLowerShriekCompIso P.Coefficient a b
  let cbc := Etale.unboundedEtaleLowerShriekCompIso P.Coefficient b c
  let cr := Etale.unboundedEtaleLowerShriekCompIso P.Coefficient a (b ≫ c)
  let cl := Etale.unboundedEtaleLowerShriekCompIso P.Coefficient (a ≫ b) c ≪≫
    Etale.unboundedEtaleLowerShriekCongr P.Coefficient (Category.assoc a b c)
  have h : Functor.whiskerLeft
        (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) a) cbc.hom ≫
      cr.hom = (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight cab.hom
          (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} P.Coefficient) c) ≫ cl.hom := by
    ext M
    simpa only [cab, cbc, cr, cl, Iso.trans_hom, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.assoc] using (congr_app ha M).symm
  have hh := conjugate_composition_assoc
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient a)
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient b)
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient c)
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient (a ≫ b))
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient (b ≫ c))
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient (a ≫ b ≫ c))
    cab cbc cr cl h
  simpa only [exceptionalCompEq_conjugate, Etale.unboundedEtaleLowerShriekCongr,
    Iso.trans_refl, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, cab, cbc, cl, cr] using congr_app hh K

private theorem exceptionalCompEq_self
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    : exceptionalCompEq P f g (f ≫ g) rfl = comp P f g := by
  apply Iso.ext
  ext K
  simp [exceptionalCompEq, FiniteEtaleNormalization.congr,
    Etale.unboundedEtaleLowerShriekCongr, conjugateIsoEquiv_apply_hom]

private def sourceCompEq
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [Etale f]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (fg : X ⟶ Z) [fg.IsOver (Spec (.of P.field.k))]
    [IsSeparated fg] [LocallyOfFiniteType fg] [QuasiCompact fg]
    (w : f ≫ g = fg) :
    exceptional P fg ≅ exceptional P g ⋙ pull P f :=
  exceptionalCompEq P f g fg w ≪≫ Functor.isoWhiskerLeft (exceptional P g) (rho P f)

private theorem sourceCompEq_assoc
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {W X Y Z : Scheme.{u}}
    [W.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of P.field.k))]
    [QuasiCompact (W ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (a : W ⟶ X) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [Etale a]
    (b : X ⟶ Y) [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    [Etale b]
    (c : Y ⟶ Z) [c.IsOver (Spec (.of P.field.k))]
    [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
    (ab : W ⟶ Y) [ab.IsOver (Spec (.of P.field.k))]
    [IsSeparated ab] [LocallyOfFiniteType ab] [QuasiCompact ab]
    [Etale ab]
    (bc : X ⟶ Z) [bc.IsOver (Spec (.of P.field.k))]
    [IsSeparated bc] [LocallyOfFiniteType bc] [QuasiCompact bc]
    (abc : W ⟶ Z) [abc.IsOver (Spec (.of P.field.k))]
    [IsSeparated abc] [LocallyOfFiniteType abc] [QuasiCompact abc]
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (hl : ab ≫ c = abc) (hr : a ≫ bc = abc)
    (K : Etale.DerivedCategoryModule P.Coefficient Z)
    (hK : domain P Y ((exceptional P c).obj K)) :
    (sourceCompEq P a bc abc hr).hom.app K ≫
        (pull P a).map ((sourceCompEq P b c bc hbc).hom.app K) =
      (sourceCompEq P ab c abc hl).hom.app K ≫
        (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          a b ab hab.symm).hom.app ((exceptional P c).obj K) := by
  subst ab bc
  cases hr
  have ha := exceptionalCompEq_assoc P a b c (a ≫ b) (b ≫ c)
    (a ≫ b ≫ c) rfl rfl hl rfl K
  have hc := (finite_etale_dualizing_normalization P a).composition b
    ((exceptional P c).obj K) hK
  simp only [sourceCompEq, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← (rho P a).hom.naturality_assoc]
  calc
    _ = (exceptionalCompEq P (a ≫ b) c (a ≫ b ≫ c) hl).hom.app K ≫
        (exceptionalCompEq P a b (a ≫ b) rfl).hom.app ((exceptional P c).obj K) ≫
        (rho P a).hom.app ((exceptional P b).obj ((exceptional P c).obj K)) ≫
        (pull P a).map ((rho P b).hom.app ((exceptional P c).obj K)) := by
      simpa only [Category.assoc, Functor.comp_obj] using congrArg
        (· ≫ (rho P a).hom.app ((exceptional P b).obj ((exceptional P c).obj K)) ≫
          (pull P a).map ((rho P b).hom.app ((exceptional P c).obj K))) ha
    _ = _ := by
      simpa only [exceptionalCompEq_self, Category.assoc] using
        congrArg ((exceptionalCompEq P (a ≫ b) c (a ≫ b ≫ c) hl).hom.app K ≫ ·) hc.symm

private theorem sourceCompEq_target_assoc
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {W X Y Z : Scheme.{u}}
    [W.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of P.field.k))]
    [QuasiCompact (W ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (a : W ⟶ X) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [Etale a]
    (b : X ⟶ Y) [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (c : Y ⟶ Z) [c.IsOver (Spec (.of P.field.k))]
    [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
    (ab : W ⟶ Y) [ab.IsOver (Spec (.of P.field.k))]
    [IsSeparated ab] [LocallyOfFiniteType ab] [QuasiCompact ab]
    (bc : X ⟶ Z) [bc.IsOver (Spec (.of P.field.k))]
    [IsSeparated bc] [LocallyOfFiniteType bc] [QuasiCompact bc]
    (abc : W ⟶ Z) [abc.IsOver (Spec (.of P.field.k))]
    [IsSeparated abc] [LocallyOfFiniteType abc] [QuasiCompact abc]
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (hl : ab ≫ c = abc) (hr : a ≫ bc = abc)
    (K : Etale.DerivedCategoryModule P.Coefficient Z) :
    (sourceCompEq P a bc abc hr).hom.app K ≫
        (pull P a).map ((exceptionalCompEq P b c bc hbc).hom.app K) =
      (exceptionalCompEq P ab c abc hl).hom.app K ≫
        (sourceCompEq P a b ab hab).hom.app ((exceptional P c).obj K) := by
  simp only [sourceCompEq, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, NatTrans.comp_app, Category.assoc]
  rw [← (rho P a).hom.naturality]
  simpa only [Category.assoc, Functor.comp_obj] using congrArg
    (· ≫ (rho P a).hom.app ((exceptional P b).obj ((exceptional P c).obj K)))
    (exceptionalCompEq_assoc P a b c ab bc abc hab hbc hl hr K)

private abbrev sigmaMap
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    : ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) X).obj (omega P f)).obj
        ((pull P f).obj (omega P g)) ⟶ omega P (f ≫ g) :=
  FiniteEtaleNormalization.sigma P.Coefficient f g
      (cf := compactification P f) (cg := compactification P g)
      (cfg := compactification P (f ≫ g)) (comp P f g)

private def targetRestriction
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [Etale g] : omega P (f ≫ g) ≅ omega P f :=
  (comp P f g).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Z) ≪≫
    (exceptional P f).mapIso (eta P g)

private theorem targetRestriction_hom
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [Etale g] : (targetRestriction P f g).hom =
      (comp P f g).hom.app
        (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Z) ≫
        (exceptional P f).map (eta P g).hom := rfl

private theorem sigma_target_restriction_aux
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {W X Y Z : Scheme.{u}}
    [W.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of P.field.k))]
    [QuasiCompact (W ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : W ⟶ X) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : X ⟶ Y) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Y ⟶ Z) [c.IsOver (Spec (.of P.field.k))]
    [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
    [Etale c] :
    sigmaMap P f (g ≫ c) ≫
        (exceptionalCompEq P (f ≫ g) c (f ≫ g ≫ c) (Category.assoc f g c)).hom.app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Z) ≫
        (exceptional P (f ≫ g)).map (eta P c).hom =
      Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient) (𝟙 (omega P f))
        ((pull P f).map (targetRestriction P g c).hom) ≫ sigmaMap P f g := by
  let := compactification P f
  let := compactification P g
  let := compactification P c
  let := compactification P (f ≫ g)
  let := compactification P (g ≫ c)
  let := compactification P (f ≫ g ≫ c)
  let C := ModuleCat.{u + 1} P.Coefficient
  let K := coefficientUnit C Z
  have ha := exceptionalCompEq_assoc P f g c (f ≫ g) (g ≫ c)
    (f ≫ g ≫ c) rfl rfl (Category.assoc f g c) rfl K
  simp only [exceptionalCompEq_self] at ha
  have hc : (comp P f (g ≫ c)).inv.app K ≫
      (exceptionalCompEq P (f ≫ g) c (f ≫ g ≫ c) (Category.assoc f g c)).hom.app K =
      (exceptional P f).map ((comp P g c).hom.app K) ≫
        (comp P f g).inv.app ((exceptional P c).obj K) := by
    apply (cancel_epi ((comp P f (g ≫ c)).hom.app K)).1
    apply (cancel_mono ((comp P f g).hom.app ((exceptional P c).obj K))).1
    simpa only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app,
      Category.comp_id, Functor.comp_obj] using ha.symm
  have hn := (comp P f g).inv.naturality (eta P c).hom
  simp only [Functor.comp_map] at hn
  have ht := tensor_naturality
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient f)
    ((targetRestriction P g c).hom)
  simp only [sigmaMap, FiniteEtaleNormalization.sigma, Category.assoc]
  rw [reassoc_of% hc]
  dsimp only [omega, Etale.dualizingComplex, Functor.comp_obj] at hn ⊢
  erw [← hn]
  rw [← Functor.map_comp_assoc]
  change Etale.dualizingComplexTensorMap P.Coefficient f (omega P (g ≫ c)) ≫
      (exceptional P f).map (targetRestriction P g c).hom ≫ _ = _
  simp only [Etale.derivedTensorHom, Etale.derivedTensor_map_app,
    Etale.derivedTensor_obj_map, id_whiskerRight]
  erw [Category.id_comp]
  simpa only [Etale.dualizingComplexTensorMap, Category.assoc,
    Functor.comp_obj, omega, Etale.dualizingComplex, exceptional, pull, coefficientUnit, C]
    using congrArg (· ≫ (comp P f g).inv.app (coefficientUnit C Y)) ht.symm

private theorem sigma_target_restriction
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {W X Y Z : Scheme.{u}}
    [W.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of P.field.k))]
    [QuasiCompact (W ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : W ⟶ X) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : X ⟶ Y) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (c : Y ⟶ Z) [c.IsOver (Spec (.of P.field.k))]
    [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
    [Etale c] :
    sigmaMap P f (g ≫ c) ≫
        (FiniteEtaleNormalization.congr P (f ≫ (g ≫ c)) ((f ≫ g) ≫ c)
          (Category.assoc f g c).symm).hom.app
            (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Z) ≫
        (comp P (f ≫ g) c).hom.app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Z) ≫
        (exceptional P (f ≫ g)).map (eta P c).hom =
      Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient) (𝟙 (omega P f))
        ((pull P f).map (targetRestriction P g c).hom) ≫ sigmaMap P f g := by
  have h := sigma_target_restriction_aux P f g c
  simp only [exceptionalCompEq, Iso.trans_hom, NatTrans.comp_app] at h
  rw [Category.assoc
    ((FiniteEtaleNormalization.congr P (f ≫ (g ≫ c)) ((f ≫ g) ≫ c)
      (Category.assoc f g c).symm).hom.app
        (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Z))
    ((comp P (f ≫ g) c).hom.app
      (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Z))
    ((exceptional P (f ≫ g)).map (eta P c).hom)] at h
  exact h

private theorem middle_unit_contraction
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D)
    (δ : ∀ B M : C, F.obj (B ⊗ M) ≅ F.obj B ⊗ F.obj M)
    (ε : F.obj (𝟙_ C) ≅ 𝟙_ D)
    (hn : ∀ {B B' : C} (m : B ⟶ B') (M : C),
      F.map (m ▷ M) ≫ (δ B' M).hom = (δ B M).hom ≫ F.map m ▷ F.obj M)
    (hu : ∀ M : C, (δ (𝟙_ C) M).hom ≫ ε.hom ▷ F.obj M ≫
      (λ_ (F.obj M)).hom = F.map (λ_ M).hom)
    (A : D) (B M : C) (η : B ⟶ 𝟙_ C) :
    (A ◁ (F.map η ≫ ε.hom) ≫ (ρ_ A).hom) ▷ F.obj M =
      (α_ A (F.obj B) (F.obj M)).hom ≫ A ◁ (δ B M).inv ≫
        A ◁ F.map (η ▷ M ≫ (λ_ M).hom) := by
  have hc : (δ B M).inv ≫ F.map (η ▷ M ≫ (λ_ M).hom) =
      (F.map η ≫ ε.hom) ▷ F.obj M ≫ (λ_ (F.obj M)).hom := by
    apply (cancel_epi (δ B M).hom).1
    simp only [Category.assoc, Iso.hom_inv_id_assoc, comp_whiskerRight]
    rw [← reassoc_of% (hn η M), hu]
    exact F.map_comp _ _
  rw [← whiskerLeft_comp, hc]
  generalize F.map η ≫ ε.hom = m
  simp only [comp_whiskerRight, whiskerLeft_comp]
  rw [← triangle, associator_naturality_middle_assoc]

private theorem cocycle_unit_reduction
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D]
    (F : C ⥤ D)
    (δ : ∀ B M : C, F.obj (B ⊗ M) ≅ F.obj B ⊗ F.obj M)
    (ε : F.obj (𝟙_ C) ≅ 𝟙_ D)
    (hn : ∀ {B B' : C} (m : B ⟶ B') (M : C),
      F.map (m ▷ M) ≫ (δ B' M).hom = (δ B M).hom ≫ F.map m ▷ F.obj M)
    (hu : ∀ M : C, (δ (𝟙_ C) M).hom ≫ ε.hom ▷ F.obj M ≫
      (λ_ (F.obj M)).hom = F.map (λ_ M).hom)
    (A A' P Q : D) (B M N : C) (η : B ⟶ 𝟙_ C)
    (s : A ⊗ F.obj B ≅ A') (T : A' ≅ A) (q : P ≅ F.obj M)
    (t : B ⊗ M ⟶ N) (E : N ≅ M)
    (z : A' ⊗ P ⟶ Q) (w : A ⊗ F.obj N ⟶ Q)
    (hs : s.hom ≫ T.hom = A ◁ (F.map η ≫ ε.hom) ≫ (ρ_ A).hom)
    (ht : t ≫ E.hom = η ▷ M ≫ (λ_ M).hom)
    (h : (s.hom ⊗ₘ 𝟙 P) ≫ z =
      (α_ A (F.obj B) P).hom ≫
        A ◁ ((F.obj B) ◁ q.hom ≫ (δ B M).inv ≫ F.map t) ≫ w) :
    z = (T.hom ⊗ₘ q.hom) ≫ A ◁ F.map E.inv ≫ w := by
  have ht' : t = (η ▷ M ≫ (λ_ M).hom) ≫ E.inv := by
    rw [← ht]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hc : (α_ A (F.obj B) P).hom ≫
      A ◁ ((F.obj B) ◁ q.hom ≫ (δ B M).inv ≫
        F.map (η ▷ M ≫ (λ_ M).hom)) =
      (A ◁ (F.map η ≫ ε.hom) ≫ (ρ_ A).hom) ⊗ₘ q.hom := by
    simp only [whiskerLeft_comp, Category.assoc]
    rw [← associator_naturality_right_assoc]
    rw [← middle_unit_contraction F δ ε hn hu A B M η]
    simpa only [whiskerLeft_comp, Category.assoc] using
      (tensorHom_def' (A ◁ (F.map η ≫ ε.hom) ≫ (ρ_ A).hom) q.hom).symm
  apply (cancel_epi (s.hom ⊗ₘ 𝟙 P)).1
  calc
    _ = (α_ A (F.obj B) P).hom ≫
        A ◁ ((F.obj B) ◁ q.hom ≫ (δ B M).inv ≫ F.map t) ≫ w := h
    _ = ((A ◁ (F.map η ≫ ε.hom) ≫ (ρ_ A).hom) ⊗ₘ q.hom) ≫
        A ◁ F.map E.inv ≫ w := by
      rw [ht', F.map_comp]
      simpa only [whiskerLeft_comp, Category.assoc] using
        congrArg (· ≫ A ◁ F.map E.inv ≫ w) hc
    _ = _ := by
      symm
      rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp, hs]

private theorem sigma_target_unit
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [Etale g] :
    sigmaMap P f g ≫ (targetRestriction P f g).hom =
      (targetUnit P.Coefficient f g (cf := compactification P f)
        (ce := compactification P g) (rho P g)).hom := by
  let := compactification P f
  let := compactification P g
  let := compactification P (f ≫ g)
  have hn := tensor_naturality
    (Etale.rightDerivedUpperShriekAdjunction P.Coefficient f) (eta P g).hom
  have hu := (WeilConjectures.PurityFiniteSetting.dualizingTensor_unit P f).1
  simp only [sigmaMap, FiniteEtaleNormalization.sigma, targetRestriction,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  change Etale.dualizingComplexTensorMap P.Coefficient f (omega P g) ≫
      (exceptional P f).map (eta P g).hom = _
  change _ ≫ Etale.dualizingComplexTensorMap P.Coefficient f
    (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Y) = _ at hn
  erw [← hn]
  rw [hu]
  simp only [targetUnit, eta, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Etale.derivedTensor_obj_map, Etale.derivedTensorRightUnitor,
    whiskerLeft_comp, Category.assoc, omega, Etale.dualizingComplex,
    coefficientUnit, exceptional, pull]

private theorem exceptional_congr_refl
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    : FiniteEtaleNormalization.congr P f f rfl = Iso.refl _ := by
  apply Iso.ext
  ext K
  simp [FiniteEtaleNormalization.congr, Etale.unboundedEtaleLowerShriekCongr,
    conjugateIsoEquiv_apply_hom]

private theorem sourceEtale_open_restriction
    (P : WeilConjectures.PurityFiniteSetting.{u}) :
    ∀
    {X Y Z X₀ Y₀ Z₀ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [X₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₀ ↘ Spec (.of P.field.k))]
    [Y₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₀ ↘ Spec (.of P.field.k))]
    [Z₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z₀ ↘ Spec (.of P.field.k))]
    (e : X ⟶ Y) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    (h : Y ⟶ Z) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (dh : ℕ) [SmoothOfRelativeDimension dh h]
    (e₀ : X₀ ⟶ Y₀) [e₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated e₀] [LocallyOfFiniteType e₀] [QuasiCompact e₀]
    [Etale e₀]
    (h₀ : Y₀ ⟶ Z₀) [h₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₀] [LocallyOfFiniteType h₀] [QuasiCompact h₀]
    (dh₀ : ℕ) [SmoothOfRelativeDimension dh₀ h₀]
    (a : X₀ ⟶ X) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [IsOpenImmersion a]
    (b : Y₀ ⟶ Y) [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    [IsOpenImmersion b]
    (c : Z₀ ⟶ Z) [c.IsOver (Spec (.of P.field.k))]
    [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
    [IsOpenImmersion c]
    (sqe : CommSq a e₀ e b) (sqh : CommSq b h₀ h c),
    (pull P a).map (sourceEtale P e h).hom ≫
      (((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          a e (e₀ ≫ b) (sqe).w.symm).symm ≪≫
        Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) e₀ b)).hom.app (omega P
        h) ≫
      (pull P e₀).map (((sourceEtale P b h).symm ≪≫
        (FiniteEtaleNormalization.congr P (b ≫ h) (h₀ ≫ c) (sqh).w).app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (comp P h₀ c).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (exceptional P h₀).mapIso (eta P c))).hom =
    (((sourceEtale P a (e ≫ h)).symm ≪≫
        (FiniteEtaleNormalization.congr P (a ≫ (e ≫ h)) ((e₀ ≫ h₀) ≫ c) ((sqe.vert_comp sqh)).w).app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (comp P (e₀ ≫ h₀) c).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (exceptional P (e₀ ≫ h₀)).mapIso (eta P c))).hom ≫
      (sourceEtale P e₀ h₀).hom := by
  intro X Y Z X₀ Y₀ Z₀ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    e _ _ _ _ _ h _ _ _ _ dh _ e₀ _ _ _ _ _ h₀ _ _ _ _ dh₀ _
    a _ _ _ _ _ b _ _ _ _ _ c _ _ _ _ _ sqe sqh
  let C := ModuleCat.{u + 1} P.Coefficient
  let K := coefficientUnit C Z
  have := P.finiteComparedInvertibleExponent (Y ↘ Spec (.of P.field.k))
  let := compactification P h
  have hK : domain P Y (omega P h) :=
    DerivedCategory.constructibleFiniteTor_mapDerivedCategory P.Coefficient
      (Etale.boundedConstructibleFiniteTor_dualizingComplex P.Coefficient dh h)
  have hl : (e₀ ≫ b) ≫ h = a ≫ (e ≫ h) := by
    rw [← sqe.w, Category.assoc]
  have hr : e₀ ≫ (b ≫ h) = a ≫ (e ≫ h) := by
    rw [← Category.assoc, hl]
  have htotal := (sqe.vert_comp sqh).w.symm
  have h₁ := sourceCompEq_assoc P a e h (e₀ ≫ b) (e ≫ h)
    (a ≫ (e ≫ h)) sqe.w rfl hl rfl K hK
  have h₂ := sourceCompEq_assoc P e₀ b h (e₀ ≫ b) (b ≫ h)
    (a ≫ (e ≫ h)) rfl rfl hl hr K hK
  have h₃ := sourceCompEq_target_assoc P e₀ h₀ c (e₀ ≫ h₀) (b ≫ h)
    (a ≫ (e ≫ h)) rfl sqh.w.symm htotal hr K
  have hn := (sourceCompEq P e₀ h₀ (e₀ ≫ h₀) rfl).hom.naturality (eta P c).hom
  simp only [Functor.comp_map] at hn
  -- Precompose with the source comparison, which is invertible.
  apply (cancel_epi (sourceEtale P a (e ≫ h)).hom).1
  simp only [Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc, NatTrans.comp_app]
  simp only [Iso.hom_inv_id_assoc]
  -- Both source-composition routes factor through the common map e₀ ≫ b.
  have hs₁ : (sourceEtale P a (e ≫ h)).hom ≫
      (pull P a).map (sourceEtale P e h).hom =
      (sourceCompEq P (e₀ ≫ b) h (a ≫ (e ≫ h)) hl).hom.app K ≫
        (Etale.leftDerivedUpperStarComp C a e (e₀ ≫ b) sqe.w.symm).hom.app
          (omega P h) := by
    simpa only [sourceCompEq, exceptionalCompEq_self, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, NatTrans.comp_app,
      sourceEtale, Iso.app_hom, K, C, Functor.comp_obj, omega,
      Etale.dualizingComplex] using h₁
  have hs₂ : (sourceCompEq P e₀ (b ≫ h) (a ≫ (e ≫ h)) hr).hom.app K ≫
      (pull P e₀).map (sourceEtale P b h).hom =
      (sourceCompEq P (e₀ ≫ b) h (a ≫ (e ≫ h)) hl).hom.app K ≫
        (Etale.leftDerivedUpperStarComp C e₀ b).hom.app (omega P h) := by
    simpa only [sourceCompEq, exceptionalCompEq_self, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, NatTrans.comp_app,
      sourceEtale, Iso.app_hom, K, C, Functor.comp_obj, omega,
      Etale.dualizingComplex] using h₂
  rw [reassoc_of% hs₁]
  simp only [Functor.comp_obj, omega, Etale.dualizingComplex, C,
    Iso.hom_inv_id_app_assoc]
  erw [← reassoc_of% hs₂]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_assoc]
  have he := congrArg
    (· ≫ (pull P e₀).map ((exceptional P h₀).map (eta P c).hom)) h₃
  simp only [Category.assoc] at he
  erw [← hn] at he
  simpa only [exceptionalCompEq, sourceCompEq, exceptionalCompEq_self,
    exceptional_congr_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.map_comp, sourceEtale, Iso.app_hom,
    Category.assoc, C, K, Functor.comp_obj, omega, Etale.dualizingComplex] using he

private def openSquarePull
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X X₀ Y Y₀ : Scheme.{u}}
    (e : X₀ ⟶ X) (f₀ : X₀ ⟶ Y₀) (f : X ⟶ Y) (a : Y₀ ⟶ Y)
    (sq : CommSq e f₀ f a) :
    pull P f ⋙ pull P e ≅ pull P a ⋙ pull P f₀ :=
  (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
    e f (f₀ ≫ a) sq.w.symm).symm ≪≫
      Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f₀ a

private def SigmaIsIsoCore
    (P : WeilConjectures.PurityFiniteSetting.{u})
    : Prop :=
  ∀
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (df : ℕ) [SmoothOfRelativeDimension df f]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (dg : ℕ) [SmoothOfRelativeDimension dg g],
    IsIso ((FiniteEtaleNormalization.sigma P.Coefficient
      f g (cf := compactification P f)
      (cg := compactification P g)
      (cfg := compactification P (f ≫ g))
      (comp P f g)))

private def SourceBaseChangeCore
    (P : WeilConjectures.PurityFiniteSetting.{u})
    : Prop :=
  ∀
    {X Y X₀ Y₀ U U₀ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [X₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₀ ↘ Spec (.of P.field.k))]
    [Y₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₀ ↘ Spec (.of P.field.k))]
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [U₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (U₀ ↘ Spec (.of P.field.k))]
    (h : X ⟶ Y) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (dh : ℕ) [SmoothOfRelativeDimension dh h]
    (h₀ : X₀ ⟶ Y₀) [h₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₀] [LocallyOfFiniteType h₀] [QuasiCompact h₀]
    (dh₀ : ℕ) [SmoothOfRelativeDimension dh₀ h₀]
    (v : Y₀ ⟶ Y) [v.IsOver (Spec (.of P.field.k))]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (u : X₀ ⟶ X) [u.IsOver (Spec (.of P.field.k))]
    [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    (e₀ : U₀ ⟶ X₀) [e₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated e₀] [LocallyOfFiniteType e₀] [QuasiCompact e₀]
    [Etale e₀]
    (u₁ : U₀ ⟶ U) [u₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated u₁] [LocallyOfFiniteType u₁] [QuasiCompact u₁]
    (sqh : IsPullback u h₀ h v) (sqe : IsPullback u₁ e₀ e u),
    beta P (e ≫ h) (e₀ ≫ h₀) v u₁ (sqe.paste_vert sqh) ≫
        (sourceEtale P e₀ h₀).hom =
      (pull P u₁).map (sourceEtale P e h).hom ≫
        (openSquarePull P u₁ e₀ e u sqe.toCommSq).hom.app (omega P h) ≫
        (pull P e₀).map (beta P h h₀ v u sqh)

private def SigmaBaseChangeCore
    (P : WeilConjectures.PurityFiniteSetting.{u})
    : Prop :=
  ∀
    {X Y Z X₀ Y₀ Z₀ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [X₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₀ ↘ Spec (.of P.field.k))]
    [Y₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₀ ↘ Spec (.of P.field.k))]
    [Z₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z₀ ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (df : ℕ) [SmoothOfRelativeDimension df f]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (dg : ℕ) [SmoothOfRelativeDimension dg g]
    (f₀ : X₀ ⟶ Y₀) [f₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated f₀] [LocallyOfFiniteType f₀] [QuasiCompact f₀]
    (df₀ : ℕ) [SmoothOfRelativeDimension df₀ f₀]
    (g₀ : Y₀ ⟶ Z₀) [g₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated g₀] [LocallyOfFiniteType g₀] [QuasiCompact g₀]
    (dg₀ : ℕ) [SmoothOfRelativeDimension dg₀ g₀]
    (a : X₀ ⟶ X) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    (b : Y₀ ⟶ Y) [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (c : Z₀ ⟶ Z) [c.IsOver (Spec (.of P.field.k))]
    [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
    (sqf : IsPullback a f₀ f b) (sqg : IsPullback b g₀ g c),
    (pull P a).map ((FiniteEtaleNormalization.sigma P.Coefficient
      f g (cf := compactification P f)
      (cg := compactification P g)
      (cfg := compactification P (f ≫ g))
      (comp P f g))) ≫
      beta P (f ≫ g) (f₀ ≫ g₀) c a (sqf.paste_vert sqg) =
    (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) a
      (omega P f) ((pull P f).obj (omega P g))).hom ≫
    Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient)
      (beta P f f₀ b a sqf)
      ((openSquarePull P a f₀ f b sqf.toCommSq).hom.app (omega P g) ≫
        (pull P f₀).map (beta P g g₀ c b sqg)) ≫
      (FiniteEtaleNormalization.sigma P.Coefficient
      f₀ g₀ (cf := compactification P f₀)
      (cg := compactification P g₀)
      (cfg := compactification P (f₀ ≫ g₀))
      (comp P f₀ g₀))

private theorem open_square_pull_transport
    (A : Type v) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
    [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    {X X₀ Y Y₀ : Scheme.{u}} (a : X₀ ⟶ X) (f₀ : X₀ ⟶ Y₀)
    (f : X ⟶ Y) (b : Y₀ ⟶ Y) (sq : CommSq a f₀ f b) :
    ((Etale.leftDerivedUpperStarComp A a f (f₀ ≫ b) sq.w.symm).symm ≪≫
      Etale.leftDerivedUpperStarComp A f₀ b).hom =
    (Etale.derivedSquareUpperStarIso A sq).inv := by
  unfold Etale.derivedSquareUpperStarIso
  rw [← Etale.leftDerivedUpperStarComp_symm_trans_eqToIso,
    ← Etale.leftDerivedUpperStarComp_symm_trans_eqToIso]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv]
  simp only [Category.assoc, eqToIso.hom, eqToHom_trans]
  apply congrArg (fun t ↦ (Etale.leftDerivedUpperStarComp A a f).inv ≫ t)
  have ht (k : X₀ ⟶ Y) (w : k = f₀ ≫ b) :
      eqToHom (congrArg (fun z ↦ (Etale.upperStar A z).leftDerivedFunctor) w) ≫
        (Etale.leftDerivedUpperStarComp A f₀ b).hom =
      (Etale.leftDerivedUpperStarComp A f₀ b k w).hom := by
    cases w
    simp
  exact ht (a ≫ f) sq.w

private theorem normalized_tensor_square_core
    {C D : Type*} [Category* C] [Category* D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D)
    (δ : ∀ A B : C, F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B)
    (ε : F.obj (𝟙_ C) ≅ 𝟙_ D)
    (hn : ∀ {A A' : C} (f : A ⟶ A') (B : C),
      F.map (f ▷ B) ≫ (δ A' B).hom = (δ A B).hom ≫ F.map f ▷ F.obj B)
    (hu : ∀ B : C, (δ (𝟙_ C) B).hom ≫ ε.hom ▷ F.obj B ≫
      (λ_ (F.obj B)).hom = F.map (λ_ B).hom)
    {M N : C} {M₀ N₀ : D} (η : M ⟶ 𝟙_ C) (η₀ : M₀ ⟶ 𝟙_ D)
    (b : F.obj M ⟶ M₀) (q : F.obj N ⟶ N₀)
    (hη : b ≫ η₀ = F.map η ≫ ε.hom) :
    (δ M N).hom ≫ (b ⊗ₘ q) ≫ η₀ ▷ N₀ ≫ (λ_ N₀).hom =
      F.map (η ▷ N ≫ (λ_ N).hom) ≫ q := by
  simp only [MonoidalCategory.tensorHom_def, Category.assoc]
  rw [whisker_exchange_assoc, ← comp_whiskerRight_assoc, hη,
    comp_whiskerRight_assoc, ← reassoc_of% (hn η N),
    leftUnitor_naturality, reassoc_of% (hu N), F.map_comp, Category.assoc]

set_option maxRecDepth 2048 in
private theorem sigma_isIso_core (P : WeilConjectures.PurityFiniteSetting.{u}) :
    SigmaIsIsoCore P := by
  intro X Y Z _ _ _ _ _ _ _ _ _ f _ _ _ _ df _ g _ _ _ _ dg _
  let := compactification P f
  let := compactification P g
  let := compactification P (f ≫ g)
  have := P.finiteComparedInvertibleExponent (X ↘ Spec (.of P.field.k))
  have ht := (Etale.exists_dualizingComplex_iso_and_tensor P.Coefficient f df).choose_spec.2.2.2
    (omega P g)
  change IsIso (Etale.dualizingComplexTensorMap P.Coefficient f (omega P g)) at ht
  have := ht
  change IsIso (Etale.dualizingComplexTensorMap P.Coefficient f (omega P g) ≫
    (comp P f g).inv.app _)
  infer_instance

set_option maxRecDepth 2048 in
private theorem sigma_base_change_core (P : WeilConjectures.PurityFiniteSetting.{u}) :
    SigmaBaseChangeCore P := by
  intro X Y Z X₀ Y₀ Z₀ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    f _ _ _ _ df _ g _ _ _ _ dg _ f₀ _ _ _ _ df₀ _ g₀ _ _ _ _ dg₀ _
    a _ _ _ _ b _ _ _ _ c _ _ _ _ sqf sqg
  have hc : SmoothExceptionalPasting.Ctf P.Coefficient Z
      (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Z) :=
    DerivedCategory.constructibleFiniteTor_mapDerivedCategory P.Coefficient
      (Etale.constructibleFiniteTor_unit P.Coefficient)
  have h := (SmoothExceptionalPasting.smoothExceptionalTowerPasting P f g f₀ g₀ a b c
    sqf sqg (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Z) df dg df₀ dg₀ hc).2
  have := QuasiCompact.compactSpace_of_compactSpace (Z₀ ↘ Spec (.of P.field.k))
  let := compactification P (f₀ ≫ g₀)
  have hunit : _root_.DerivedCategory.TStructure.t.plus
      (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Z₀) :=
    (Etale.constructibleFiniteTor_unit P.Coefficient).1.1.1
  have hp := Etale.plus_rightDerivedUpperShriek_obj
    P.Coefficient (f₀ ≫ g₀) _ hunit
  apply (bijective_comparisonUpperStar_mapDerivedCategory_map _ _ hp).1
  have hsq : (openSquarePull P a f₀ f b sqf.toCommSq).hom =
      (Etale.derivedSquareUpperStarIso
        (ModuleCat.{u + 1} P.Coefficient) sqf.toCommSq).inv :=
    open_square_pull_transport (ModuleCat.{u + 1} P.Coefficient) a f₀ f b sqf.toCommSq
  change _ = _ at h
  change _ = _
  simp only [Etale.derivedTensorHom, Category.assoc]
  rw [hsq]
  exact h

set_option maxRecDepth 2048 in
private theorem source_base_change_core (P : WeilConjectures.PurityFiniteSetting.{u}) :
    SourceBaseChangeCore P := by
  intro X Y X₀ Y₀ U U₀ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    h _ _ _ _ dh _ h₀ _ _ _ _ dh₀ _ v _ _ _ _ u _ _ _ _
    e _ _ _ _ _ e₀ _ _ _ _ _ u₁ _ _ _ _ sqh sqe
  let := SmoothOfRelativeDimension.smooth dh h
  let := SmoothOfRelativeDimension.smooth dh₀ h₀
  let := compactification P e
  let := compactification P e₀
  let := compactification P h
  let := compactification P h₀
  let := compactification P (e ≫ h)
  let := compactification P (e₀ ≫ h₀)
  have he := (finite_etale_dualizing_normalization P e).source_etale h
  have he₀ := (finite_etale_dualizing_normalization P e₀).source_etale h₀
  change FiniteEtaleNormalization.sigma _ e h (comp P e h) ≫
      (sourceEtale P e h).hom = tensorUnitMap _ U _ _ (eta P e) at he
  change FiniteEtaleNormalization.sigma _ e₀ h₀ (comp P e₀ h₀) ≫
      (sourceEtale P e₀ h₀).hom = tensorUnitMap _ U₀ _ _ (eta P e₀) at he₀
  have hη := (finite_etale_dualizing_normalization P e).eta_base_change e₀ u u₁ sqe
  have hsb := sigma_base_change_core P e 0 h dh e₀ 0 h₀ dh₀ u₁ u v sqe sqh
  have := sigma_isIso_core P e 0 h dh
  apply (cancel_epi ((pull P u₁).map
    (FiniteEtaleNormalization.sigma _ e h (comp P e h)))).1
  erw [← Category.assoc, hsb]
  simp only [Category.assoc]
  rw [he₀, ← Functor.map_comp_assoc, he]
  let q := (openSquarePull P u₁ e₀ e u sqe.toCommSq).hom.app (omega P h) ≫
    (pull P e₀).map (beta P h h₀ v u sqh)
  have hu (N : Etale.DerivedCategoryModule P.Coefficient U) :=
    Etale.leftDerivedUpperStarTensorComparison_leftUnitor_hom
      (ModuleCat.{u + 1} P.Coefficient) u₁ N
  have hn := normalized_tensor_square_core (pull P u₁)
    (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) u₁)
    (Etale.leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} P.Coefficient) u₁)
    (fun φ N ↦ Etale.leftDerivedUpperStarTensorIso_hom_naturality_left u₁ φ N)
    hu (eta P e).hom (eta P e₀).hom (beta P e e₀ u u₁ sqe) q hη
  simpa only [q, tensorUnitMap, Etale.derivedTensor_map_app,
    Etale.derivedTensorHom, Etale.derivedTensor_obj_map, MonoidalCategory.tensorHom_def,
    Etale.derivedTensorLeftUnitor, Category.assoc] using hn

private theorem sigma_middle_etale
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {W X Y Z : Scheme.{u}}
    [W.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of P.field.k))]
    [QuasiCompact (W ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : W ⟶ X) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (df : ℕ) [SmoothOfRelativeDimension df f]
    (g : X ⟶ Y) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [Etale g]
    (c : Y ⟶ Z) [c.IsOver (Spec (.of P.field.k))]
    [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
    (dc : ℕ) [SmoothOfRelativeDimension dc c] :
    sigmaMap P (f ≫ g) c ≫
        (FiniteEtaleNormalization.congr P ((f ≫ g) ≫ c) (f ≫ g ≫ c)
          (Category.assoc f g c)).hom.app
            (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Z) =
      Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient)
        (targetRestriction P f g).hom
        ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          f g).hom.app (omega P c)) ≫
        ((Etale.derivedTensor (ModuleCat.{u + 1} P.Coefficient) W).obj (omega P f)).map
          ((pull P f).map (sourceEtale P g c).inv) ≫ sigmaMap P f (g ≫ c) := by
  let := SmoothOfRelativeDimension.smooth df f
  let := SmoothOfRelativeDimension.smooth dc c
  have := sigma_isIso_core P f df g 0
  let C := ModuleCat.{u + 1} P.Coefficient
  let s := asIso (sigmaMap P f g)
  let T := targetRestriction P f g
  let q := (Etale.leftDerivedUpperStarComp C f g).app (omega P c)
  have hsrc := (finite_etale_dualizing_normalization P g).source_etale c
  change sigmaMap P g c ≫ (sourceEtale P g c).hom =
    tensorUnitMap C X (omega P g)
      ((pull P g).obj (omega P c)) (eta P g) at hsrc
  have htarget := sigma_target_unit P f g
  have hcoc := (dualizing_cocycle_source_etale P).1 f df g 0 c dc
  have hunit := Etale.leftDerivedUpperStarTensorComparison_leftUnitor_hom C f
  have h := cocycle_unit_reduction (pull P f)
    (Etale.leftDerivedUpperStarTensorIso C f) (Etale.leftDerivedUpperStarUnitIso C f)
    (fun φ N ↦ Etale.leftDerivedUpperStarTensorIso_hom_naturality_left f φ N)
    hunit (omega P f) (omega P (f ≫ g)) ((pull P (f ≫ g)).obj (omega P c))
    (omega P (f ≫ g ≫ c)) (omega P g) ((pull P g).obj (omega P c))
    (omega P (g ≫ c)) (eta P g).hom s T q (sigmaMap P g c)
    (sourceEtale P g c)
    (sigmaMap P (f ≫ g) c ≫
      (FiniteEtaleNormalization.congr P ((f ≫ g) ≫ c) (f ≫ g ≫ c)
        (Category.assoc f g c)).hom.app (coefficientUnit C Z))
    (sigmaMap P f (g ≫ c))
    (by
      simpa only [s, T, C, asIso_hom, omega, Etale.dualizingComplex,
        pull, exceptional, coefficientUnit, targetUnit, eta, Iso.trans_hom, Iso.app_hom,
        Functor.mapIso_hom, Functor.map_comp, Etale.derivedTensor_obj_map,
        Etale.derivedTensorRightUnitor, Category.assoc] using htarget)
    (by
      simpa only [sigmaMap, omega, Etale.dualizingComplex, pull, exceptional,
        coefficientUnit, tensorUnitMap, Etale.derivedTensor_map_app,
        Etale.derivedTensorLeftUnitor] using hsrc)
    (by
      simp only [sigmaMap, s, q, C, asIso_hom, Iso.app_hom,
        omega, Etale.dualizingComplex, pull, exceptional, coefficientUnit,
        whiskerLeft_id, id_whiskerRight, Category.comp_id,
        whiskerLeft_comp, Etale.derivedTensorHom,
        Etale.derivedTensor_map_app, Etale.derivedTensor_obj_map,
        Etale.derivedTensorAssociator, MonoidalCategory.tensorHom_def, Category.assoc]
        at hcoc ⊢
      erw [Category.id_comp, whiskerLeft_id, Category.id_comp] at hcoc
      exact hcoc)
  simpa only [s, T, q, C, Iso.app_hom, asIso_hom,
    omega, Etale.dualizingComplex, pull, exceptional, coefficientUnit,
    Etale.derivedTensorHom, Etale.derivedTensor_map_app,
    Etale.derivedTensor_obj_map, MonoidalCategory.tensorHom_def, Category.assoc] using h

private def pullCongr (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f g : X ⟶ Y) (w : f = g) : pull P f ≅ pull P g :=
  eqToIso (congrArg (pull P) w)

private theorem eqToIso_symm_generic {C : Type*} [Category* C] {X Y : C}
    (h : X = Y) : (eqToIso h).symm = eqToIso h.symm := by
  apply Iso.ext
  rfl

private theorem pullCongr_symm (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}} (f g : X ⟶ Y) (w : f = g) :
    (pullCongr P f g w).symm = pullCongr P g f w.symm := by
  exact eqToIso_symm_generic (congrArg (pull P) w)

private theorem pullComp_eq (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (w : fg = f ≫ g) :
    Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f g fg w =
      pullCongr P fg (f ≫ g) w ≪≫
        Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f g := by
  subst fg
  change _ = Iso.refl _ ≪≫ _
  exact (Iso.refl_trans _).symm

private theorem openSquarePull_canonical (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y X₀ Y₀ : Scheme.{u}} (a : X₀ ⟶ X) (f₀ : X₀ ⟶ Y₀)
    (f : X ⟶ Y) (b : Y₀ ⟶ Y) (sq : CommSq a f₀ f b) :
    ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      a f (f₀ ≫ b) sq.w.symm).symm ≪≫
      Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f₀ b) =
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) a f).symm ≪≫
      pullCongr P (a ≫ f) (f₀ ≫ b) sq.w ≪≫
      Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f₀ b := by
  rw [pullComp_eq, Iso.trans_symm, pullCongr_symm, Iso.trans_assoc]

private theorem sigma_eq_left
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (f' : X ⟶ Y) [f'.IsOver (Spec (.of P.field.k))]
    [IsSeparated f'] [LocallyOfFiniteType f'] [QuasiCompact f'] (hf : f = f') :
    sigmaMap P f g ≫
        (FiniteEtaleNormalization.congr P (f ≫ g) (f' ≫ g)
          (by rw [hf])).hom.app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Z) =
      Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient)
        ((FiniteEtaleNormalization.congr P f f' hf).hom.app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Y))
        ((pullCongr P f f' hf).hom.app (omega P g)) ≫ sigmaMap P f' g := by
  subst f'
  simp only [exceptional_congr_refl, pullCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app]
  change sigmaMap P f g ≫ 𝟙 (omega P (f ≫ g)) =
    Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient)
      (𝟙 (omega P f)) (𝟙 ((pull P f).obj (omega P g))) ≫ sigmaMap P f g
  erw [Etale.derivedTensorHom_id, Category.id_comp, Category.comp_id]

private theorem sigma_eq_right
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y Z : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (g' : Y ⟶ Z) [g'.IsOver (Spec (.of P.field.k))]
    [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g'] (hg : g = g') :
    sigmaMap P f g ≫
        (FiniteEtaleNormalization.congr P (f ≫ g) (f ≫ g')
          (by rw [hg])).hom.app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Z) =
      Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient) (𝟙 (omega P f))
        ((pull P f).map ((FiniteEtaleNormalization.congr P g g' hg).hom.app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Z))) ≫ sigmaMap P f g' := by
  subst g'
  simp only [exceptional_congr_refl, Iso.refl_hom, NatTrans.id_app]
  change sigmaMap P f g ≫ 𝟙 (omega P (f ≫ g)) =
    Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient)
      (𝟙 (omega P f)) ((pull P f).map (𝟙 (omega P g))) ≫ sigmaMap P f g
  erw [(pull P f).map_id, Etale.derivedTensorHom_id, Category.id_comp, Category.comp_id]

private theorem exceptional_congr_trans_app
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (g : X ⟶ Y) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (h : X ⟶ Y) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (hf : f = g) (hg : g = h) (K : Etale.DerivedCategoryModule P.Coefficient Y) :
    (FiniteEtaleNormalization.congr P f g hf).hom.app K ≫
      (FiniteEtaleNormalization.congr P g h hg).hom.app K =
      (FiniteEtaleNormalization.congr P f h (hf.trans hg)).hom.app K := by
  subst g h
  simp only [exceptional_congr_refl, Iso.refl_hom, NatTrans.id_app, Category.id_comp]

private def openRestriction
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X X₀ Y Y₀ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [X₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₀ ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Y₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₀ ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (f₀ : X₀ ⟶ Y₀) [f₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated f₀] [LocallyOfFiniteType f₀] [QuasiCompact f₀]
    (e : X₀ ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    (a : Y₀ ⟶ Y) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [Etale a]
    (sq : CommSq e f₀ f a) :
    (pull P e).obj (omega P f) ≅ omega P f₀ :=
  (sourceEtale P e f).symm ≪≫
    (FiniteEtaleNormalization.congr P (e ≫ f) (f₀ ≫ a) sq.w).app
      (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Y) ≪≫
    (comp P f₀ a).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Y) ≪≫
    (exceptional P f₀).mapIso (eta P a)

private theorem openRestriction_cartesian
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X X₀ Y Y₀ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [X₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₀ ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Y₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₀ ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [Smooth f]
    (f₀ : X₀ ⟶ Y₀) [f₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated f₀] [LocallyOfFiniteType f₀] [QuasiCompact f₀]
    [Smooth f₀]
    (e : X₀ ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    (a : Y₀ ⟶ Y) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [Etale a]
    (sq : IsPullback e f₀ f a) :
    (openRestriction P f f₀ e a sq.toCommSq).hom = beta P f f₀ a e sq := by
  have h := (finite_etale_dualizing_normalization P a).smooth_base_change f f₀ e sq
  have hu := sigma_target_unit P f₀ a
  have h' := congrArg (· ≫ (targetRestriction P f₀ a).hom) h
  have hh : beta P f f₀ a e sq =
      (sourceEtale P e f).inv ≫
        (FiniteEtaleNormalization.congr P (e ≫ f) (f₀ ≫ a) sq.w).hom.app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Y) ≫
        (targetRestriction P f₀ a).hom := by
    simpa only [Category.assoc, hu, Iso.inv_hom_id, Category.comp_id] using h'
  simpa only [openRestriction, targetRestriction, Iso.trans_hom, Iso.app_hom,
    Iso.symm_hom, Functor.mapIso_hom, Category.assoc] using hh.symm

private theorem openRestriction_source_factor
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {W X Y T Z : Scheme.{u}}
    [W.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (W ↘ Spec (.of P.field.k))]
    [QuasiCompact (W ↘ Spec (.of P.field.k))]
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [T.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    (j : W ⟶ X) [j.IsOver (Spec (.of P.field.k))]
    [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    [Etale j]
    (i : X ⟶ Y) [i.IsOver (Spec (.of P.field.k))]
    [IsSeparated i] [LocallyOfFiniteType i] [QuasiCompact i]
    [Etale i]
    (h : Y ⟶ Z) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (dh : ℕ) [SmoothOfRelativeDimension dh h]
    (t : X ⟶ T) [t.IsOver (Spec (.of P.field.k))]
    [IsSeparated t] [LocallyOfFiniteType t] [QuasiCompact t]
    (b : T ⟶ Z) [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    [Etale b]
    (a : W ⟶ Y) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [Etale a]
    (h₀ : W ⟶ T) [h₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₀] [LocallyOfFiniteType h₀] [QuasiCompact h₀]
    (hji : j ≫ i = a) (hjt : j ≫ t = h₀)
    (sq : CommSq i t h b)
    (sq₀ : CommSq a h₀ h b) :
    (openRestriction P h h₀ a b sq₀).hom ≫
        (sourceCompEq P j t h₀ hjt).hom.app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) T) =
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        j i a hji.symm).hom.app (omega P h) ≫
        (pull P j).map (openRestriction P h t i b sq).hom := by
  let C := ModuleCat.{u + 1} P.Coefficient
  let K := coefficientUnit C Z
  have := P.finiteComparedInvertibleExponent (Y ↘ Spec (.of P.field.k))
  let := compactification P h
  have hK : domain P Y ((exceptional P h).obj K) := by
    exact DerivedCategory.constructibleFiniteTor_mapDerivedCategory P.Coefficient
      (Etale.boundedConstructibleFiniteTor_dualizingComplex P.Coefficient dh h)
  have hr : j ≫ (i ≫ h) = a ≫ h := by rw [← Category.assoc, hji]
  have h₁ := sourceCompEq_assoc P j i h a (i ≫ h) (a ≫ h)
    hji rfl rfl hr K hK
  have h₂ := sourceCompEq_target_assoc P j t b h₀ (i ≫ h) (a ≫ h)
    hjt sq.w.symm sq₀.w.symm hr K
  have hn := (sourceCompEq P j t h₀ hjt).hom.naturality (eta P b).hom
  simp only [Functor.comp_map] at hn
  apply (cancel_epi (sourceEtale P a h).hom).1
  simp only [openRestriction, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  have hs₁ : (sourceEtale P a h).hom ≫
      (Etale.leftDerivedUpperStarComp C j i a hji.symm).hom.app (omega P h) =
      (sourceCompEq P j (i ≫ h) (a ≫ h) hr).hom.app K ≫
        (pull P j).map (sourceEtale P i h).hom := by
    simpa only [sourceCompEq, exceptionalCompEq_self, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, NatTrans.comp_app,
      sourceEtale, Iso.app_hom, K, C, Functor.comp_obj, omega,
      Etale.dualizingComplex] using h₁.symm
  rw [reassoc_of% hs₁]
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_assoc]
  have he := congrArg
    (· ≫ (pull P j).map ((exceptional P t).map (eta P b).hom)) h₂
  simp only [Category.assoc] at he
  erw [← hn] at he
  simpa only [exceptionalCompEq, Iso.trans_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc, C, K] using he.symm

private theorem beta_eq
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y X₁ Y₁ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [X₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₁ ↘ Spec (.of P.field.k))]
    [Y₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₁ ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (f₁ : X₁ ⟶ Y₁) [f₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated f₁] [LocallyOfFiniteType f₁] [QuasiCompact f₁]
    (g : Y₁ ⟶ Y) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (g₁ : X₁ ⟶ X) [g₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated g₁] [LocallyOfFiniteType g₁] [QuasiCompact g₁]
    (g' : Y₁ ⟶ Y) [g'.IsOver (Spec (.of P.field.k))]
    [IsSeparated g'] [LocallyOfFiniteType g'] [QuasiCompact g']
    (g₁' : X₁ ⟶ X) [g₁'.IsOver (Spec (.of P.field.k))]
    [IsSeparated g₁'] [LocallyOfFiniteType g₁'] [QuasiCompact g₁']
    (hv : g = g') (hu : g₁ = g₁')
    (sq : IsPullback g₁ f₁ f g) (sq' : IsPullback g₁' f₁ f g') :
    beta P f f₁ g g₁ sq = (pullCongr P g₁ g₁' hu).hom.app (omega P f) ≫
      beta P f f₁ g' g₁' sq' := by
  subst g' g₁'
  simp [pullCongr]

private theorem rectangle_word
    {C : Type*} [Category* C] {A B D E F G Z : C}
    (c₁ : A ⟶ B) (c₁inv : B ⟶ A) (q : A ⟶ D) (c₂ : D ⟶ E)
    (hi : c₁inv ≫ c₁ = 𝟙 B)
    (f : B ⟶ F) (b : F ⟶ Z) (g : E ⟶ G) (b' : G ⟶ Z)
    (x : A ⟶ Z) (y : D ⟶ Z)
    (hf : x = c₁ ≫ f ≫ b) (he : x = q ≫ y)
    (hb : y = c₂ ≫ g ≫ b') :
    f ≫ b = (c₁inv ≫ q ≫ c₂) ≫ g ≫ b' := by
  calc
    f ≫ b = c₁inv ≫ (c₁ ≫ f ≫ b) := by rw [← Category.assoc, hi, Category.id_comp]
    _ = c₁inv ≫ x := by rw [← hf]
    _ = _ := by rw [he, hb]; simp only [Category.assoc]

private theorem openSquarePull_nat_canonical
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y X₀ Y₀ : Scheme.{u}} (a : X₀ ⟶ X) (f₀ : X₀ ⟶ Y₀)
    (f : X ⟶ Y) (b : Y₀ ⟶ Y) (sq : CommSq a f₀ f b) :
    (openSquarePull P a f₀ f b sq).hom =
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) a f).inv ≫
      (pullCongr P (a ≫ f) (f₀ ≫ b) sq.w).hom ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f₀ b).hom := by
  exact congrArg Iso.hom (openSquarePull_canonical P a f₀ f b sq)

private theorem openSquarePull_hom_canonical
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y X₀ Y₀ : Scheme.{u}} (a : X₀ ⟶ X) (f₀ : X₀ ⟶ Y₀)
    (f : X ⟶ Y) (b : Y₀ ⟶ Y) (sq : CommSq a f₀ f b)
    (K : Etale.DerivedCategoryModule P.Coefficient Y) :
    (openSquarePull P a f₀ f b sq).hom.app K =
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) a f).inv.app K ≫
      (pullCongr P (a ≫ f) (f₀ ≫ b) sq.w).hom.app K ≫
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f₀ b).hom.app K := by
  rw [openSquarePull_nat_canonical]
  rfl

private theorem beta_horizontal_paste
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y X₁ Y₁ X₂ Y₂ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [X₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₁ ↘ Spec (.of P.field.k))]
    [Y₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₁ ↘ Spec (.of P.field.k))]
    [X₂.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₂ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₂ ↘ Spec (.of P.field.k))]
    [Y₂.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₂ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₂ ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (f₁ : X₁ ⟶ Y₁) [f₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated f₁] [LocallyOfFiniteType f₁] [QuasiCompact f₁]
    (f₂ : X₂ ⟶ Y₂) [f₂.IsOver (Spec (.of P.field.k))]
    [IsSeparated f₂] [LocallyOfFiniteType f₂] [QuasiCompact f₂]
    (u : X₁ ⟶ X) [u.IsOver (Spec (.of P.field.k))]
    [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    (v : Y₁ ⟶ Y) [v.IsOver (Spec (.of P.field.k))]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (w : X₂ ⟶ X₁) [w.IsOver (Spec (.of P.field.k))]
    [IsSeparated w] [LocallyOfFiniteType w] [QuasiCompact w]
    (z : Y₂ ⟶ Y₁) [z.IsOver (Spec (.of P.field.k))]
    [IsSeparated z] [LocallyOfFiniteType z] [QuasiCompact z]
    (sq₁ : IsPullback u f₁ f v) (sq₂ : IsPullback w f₂ f₁ z) :
    beta P f f₂ (z ≫ v) (w ≫ u) (sq₂.paste_horiz sq₁) =
      (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
        w u).hom.app (omega P f) ≫
        (pull P w).map (beta P f f₁ v u sq₁) ≫ beta P f₁ f₂ z w sq₂ := by
  let := fieldSchemeNoetherian P X
  let := fieldSchemeNoetherian P Y
  let := fieldSchemeNoetherian P X₁
  let := fieldSchemeNoetherian P Y₁
  let := fieldSchemeNoetherian P X₂
  let := fieldSchemeNoetherian P Y₂
  let := compactification P f
  let := compactification P f₁
  let := compactification P f₂
  exact Etale.dualizing_base_comp P.Coefficient sq₁ sq₂

private theorem beta_rectangle
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y X₁ Y₁ T T₁ Y₀ Y₁₀ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [X₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₁ ↘ Spec (.of P.field.k))]
    [Y₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₁ ↘ Spec (.of P.field.k))]
    [T.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    [T₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (T₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (T₁ ↘ Spec (.of P.field.k))]
    [Y₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₀ ↘ Spec (.of P.field.k))]
    [Y₁₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₁₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₁₀ ↘ Spec (.of P.field.k))]
    (h : X ⟶ Y) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (h₁ : X₁ ⟶ Y₁) [h₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₁] [LocallyOfFiniteType h₁] [QuasiCompact h₁]
    (u : X₁ ⟶ X) [u.IsOver (Spec (.of P.field.k))]
    [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    (v : Y₁ ⟶ Y) [v.IsOver (Spec (.of P.field.k))]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (i : T ⟶ X) [i.IsOver (Spec (.of P.field.k))]
    [IsSeparated i] [LocallyOfFiniteType i] [QuasiCompact i]
    (t : T ⟶ Y₀) [t.IsOver (Spec (.of P.field.k))]
    [IsSeparated t] [LocallyOfFiniteType t] [QuasiCompact t]
    (i₁ : T₁ ⟶ X₁) [i₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated i₁] [LocallyOfFiniteType i₁] [QuasiCompact i₁]
    (t₁ : T₁ ⟶ Y₁₀) [t₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated t₁] [LocallyOfFiniteType t₁] [QuasiCompact t₁]
    (b : Y₀ ⟶ Y) [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    (b₁ : Y₁₀ ⟶ Y₁) [b₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated b₁] [LocallyOfFiniteType b₁] [QuasiCompact b₁]
    (U : T₁ ⟶ T) [U.IsOver (Spec (.of P.field.k))]
    [IsSeparated U] [LocallyOfFiniteType U] [QuasiCompact U]
    (v₀ : Y₁₀ ⟶ Y₀) [v₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated v₀] [LocallyOfFiniteType v₀] [QuasiCompact v₀]
    (sq : IsPullback u h₁ h v)
    (sq₀ : IsPullback i t h b) (sq₁ : IsPullback i₁ t₁ h₁ b₁)
    (sqbar : IsPullback U t₁ t v₀)
    (squ : CommSq i₁ U u i) (sqv : CommSq b₁ v₀ v b) :
    (pull P i₁).map (beta P h h₁ v u sq) ≫ beta P h₁ t₁ b₁ i₁ sq₁ =
      (openSquarePull P i₁ U u i squ).hom.app (omega P h) ≫
        (pull P U).map (beta P h t b i sq₀) ≫ beta P t t₁ v₀ U sqbar := by
  have hf := beta_horizontal_paste P h h₁ t₁ u v i₁ b₁ sq sq₁
  have hb := beta_horizontal_paste P h t t₁ i b U v₀ sq₀ sqbar
  have he := beta_eq P h t₁ (b₁ ≫ v) (i₁ ≫ u) (v₀ ≫ b) (U ≫ i)
    sqv.w squ.w (sq₁.paste_horiz sq) (sqbar.paste_horiz sq₀)
  have hc := openSquarePull_hom_canonical P i₁ U u i squ (omega P h)
  have hw := rectangle_word
    ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      i₁ u).hom.app (omega P h))
    ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      i₁ u).inv.app (omega P h))
    ((pullCongr P (i₁ ≫ u) (U ≫ i) squ.w).hom.app (omega P h))
    ((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      U i).hom.app (omega P h))
    (Iso.inv_hom_id_app (Etale.leftDerivedUpperStarComp
      (ModuleCat.{u + 1} P.Coefficient) i₁ u) (omega P h))
    ((pull P i₁).map (beta P h h₁ v u sq)) (beta P h₁ t₁ b₁ i₁ sq₁)
    ((pull P U).map (beta P h t b i sq₀)) (beta P t t₁ v₀ U sqbar)
    (beta P h t₁ (b₁ ≫ v) (i₁ ≫ u) (sq₁.paste_horiz sq))
    (beta P h t₁ (v₀ ≫ b) (U ≫ i) (sqbar.paste_horiz sq₀)) hf he hb
  rw [hc]
  exact hw

private theorem source_beta_eq
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y X₀ Y₀ U U₀ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [X₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₀ ↘ Spec (.of P.field.k))]
    [Y₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₀ ↘ Spec (.of P.field.k))]
    [U.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of P.field.k))]
    [QuasiCompact (U ↘ Spec (.of P.field.k))]
    [U₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (U₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (U₀ ↘ Spec (.of P.field.k))]
    (h : X ⟶ Y) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (dh : ℕ) [SmoothOfRelativeDimension dh h]
    (h₀ : X₀ ⟶ Y₀) [h₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₀] [LocallyOfFiniteType h₀] [QuasiCompact h₀]
    (dh₀ : ℕ) [SmoothOfRelativeDimension dh₀ h₀]
    (v : Y₀ ⟶ Y) [v.IsOver (Spec (.of P.field.k))]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (u : X₀ ⟶ X) [u.IsOver (Spec (.of P.field.k))]
    [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    (e : U ⟶ X) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    (e₀ : U₀ ⟶ X₀) [e₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated e₀] [LocallyOfFiniteType e₀] [QuasiCompact e₀]
    [Etale e₀]
    (u₁ : U₀ ⟶ U) [u₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated u₁] [LocallyOfFiniteType u₁] [QuasiCompact u₁]
    (eh : U ⟶ Y) [eh.IsOver (Spec (.of P.field.k))]
    [IsSeparated eh] [LocallyOfFiniteType eh] [QuasiCompact eh]
    (eh₀ : U₀ ⟶ Y₀) [eh₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated eh₀] [LocallyOfFiniteType eh₀] [QuasiCompact eh₀]
    (heh : e ≫ h = eh) (heh₀ : e₀ ≫ h₀ = eh₀)
    (sqh : IsPullback u h₀ h v) (sqe : IsPullback u₁ e₀ e u)
    (sq : IsPullback u₁ eh₀ eh v) :
    beta P eh eh₀ v u₁ sq ≫
        (sourceCompEq P e₀ h₀ eh₀ heh₀).hom.app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Y₀) =
      (pull P u₁).map ((sourceCompEq P e h eh heh).hom.app
        (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) Y)) ≫
        (openSquarePull P u₁ e₀ e u sqe.toCommSq).hom.app (omega P h) ≫
        (pull P e₀).map (beta P h h₀ v u sqh) := by
  subst eh eh₀
  simpa only [sourceCompEq, exceptionalCompEq_self, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, NatTrans.comp_app,
    sourceEtale, Iso.app_hom, Functor.comp_obj, omega, Etale.dualizingComplex] using
      (source_base_change_core P h dh h₀ dh₀ v u e e₀ u₁ sqh sqe)

private theorem openSquarePull_flip
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {W X Y Z : Scheme.{u}} (a : W ⟶ X) (b : W ⟶ Y)
    (p : X ⟶ Z) (e : Y ⟶ Z) (sq : CommSq a b p e) :
    (openSquarePull P a b p e sq).symm =
      openSquarePull P b a e p sq.flip := by
  unfold openSquarePull
  rw [openSquarePull_canonical P a b p e sq,
    openSquarePull_canonical P b a e p sq.flip]
  simp only [Iso.trans_symm, Iso.symm_symm_eq, pullCongr_symm, Iso.trans_assoc]

private theorem pull_square_grid
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X X₁ T T₁ X₀ X₁₀ : Scheme.{u}}
    (u : X₁ ⟶ X) (i : T ⟶ X) (i₁ : T₁ ⟶ X₁) (U : T₁ ⟶ T)
    (j : X₀ ⟶ T) (j₁ : X₁₀ ⟶ T₁) (u₀ : X₁₀ ⟶ X₀)
    (a : X₀ ⟶ X) (a₁ : X₁₀ ⟶ X₁)
    (hji : j ≫ i = a) (hji₁ : j₁ ≫ i₁ = a₁)
    (sqtarget : CommSq i₁ U u i) (sqsource : CommSq u₀ j₁ j U)
    (sqbig : CommSq a₁ u₀ u a)
    (K : Etale.DerivedCategoryModule P.Coefficient X) :
    (Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
      j₁ i₁ a₁ hji₁.symm).hom.app ((pull P u).obj K) ≫
      (pull P j₁).map ((openSquarePull P i₁ U u i sqtarget).hom.app K) =
    (openSquarePull P a₁ u₀ u a sqbig).hom.app K ≫
      (pull P u₀).map ((Etale.leftDerivedUpperStarComp
        (ModuleCat.{u + 1} P.Coefficient) j i a hji.symm).hom.app K) ≫
      (openSquarePull P u₀ j₁ j U sqsource).hom.app ((pull P i).obj K) := by
  let C := ModuleCat.{u + 1} P.Coefficient
  have hp := Etale.derivedSquareUpperStarIso_paste C sqtarget sqsource.flip sqbig
    hji₁.symm hji.symm K
  have hs (a : T₁ ⟶ X₁) (b : T₁ ⟶ T)
      (p : X₁ ⟶ X) (e : T ⟶ X) (sq : CommSq a b p e) :
      (Etale.derivedSquareUpperStarIso C sq).hom =
        (openSquarePull P a b p e sq).inv := by
    have hi : openSquarePull P a b p e sq =
        (Etale.derivedSquareUpperStarIso C sq).symm :=
      Iso.ext (open_square_pull_transport C a b p e sq)
    exact (congrArg (fun ι ↦ ι.inv) hi).symm
  have hflip : (Etale.derivedSquareUpperStarIso C sqsource.flip).hom =
      (openSquarePull P u₀ j₁ j U sqsource).hom := by
    have hi : openSquarePull P j₁ u₀ U j sqsource.flip =
        (Etale.derivedSquareUpperStarIso C sqsource.flip).symm :=
      Iso.ext (open_square_pull_transport C j₁ u₀ U j sqsource.flip)
    calc
      _ = (openSquarePull P j₁ u₀ U j sqsource.flip).inv :=
        (congrArg (fun ι ↦ ι.inv) hi).symm
      _ = _ := by rw [← openSquarePull_flip P u₀ j₁ j U sqsource]; rfl
  have hbig : (Etale.derivedSquareUpperStarIso C sqbig).hom =
      (openSquarePull P a₁ u₀ u a sqbig).inv := by
    have hi : openSquarePull P a₁ u₀ u a sqbig =
        (Etale.derivedSquareUpperStarIso C sqbig).symm :=
      Iso.ext (open_square_pull_transport C a₁ u₀ u a sqbig)
    exact (congrArg (fun ι ↦ ι.inv) hi).symm
  rw [hflip, hs i₁ U u i sqtarget, hbig] at hp
  change (pull P u₀).map
      ((Etale.leftDerivedUpperStarComp C j i a hji.symm).hom.app K) ≫
      (openSquarePull P u₀ j₁ j U sqsource).hom.app ((pull P i).obj K) ≫
      (pull P j₁).map ((openSquarePull P i₁ U u i sqtarget).inv.app K) ≫
      (Etale.leftDerivedUpperStarComp C j₁ i₁ a₁ hji₁.symm).inv.app
        ((pull P u).obj K) =
      (openSquarePull P a₁ u₀ u a sqbig).inv.app K at hp
  apply (cancel_epi ((openSquarePull P a₁ u₀ u a sqbig).inv.app K)).1
  apply (cancel_mono
    ((pull P j₁).map ((openSquarePull P i₁ U u i sqtarget).inv.app K) ≫
      (Etale.leftDerivedUpperStarComp C j₁ i₁ a₁ hji₁.symm).inv.app
        ((pull P u).obj K))).1
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp_assoc,
    Iso.hom_inv_id_app]
  erw [(pull P j₁).map_id]
  simp only [C, Category.id_comp, Iso.hom_inv_id_app]
  erw [Category.comp_id]
  simpa only [C] using hp.symm

private theorem pasting_word
    {C : Type*} [Category* C]
    {A B D E A' B' F G H I J K : C}
    (f : A ⟶ B) (r : B ⟶ D) (s : D ⟶ E) [Mono s]
    (c : B ⟶ B') (b : B' ⟶ E) (c' : A ⟶ A') (f' : A' ⟶ B')
    (p : A' ⟶ F) (u : F ⟶ G) (b' : G ⟶ E)
    (q : A ⟶ H) (v : H ⟶ I) (t : I ⟶ F)
    (w : I ⟶ J) (t' : J ⟶ G) (r' : H ⟶ K) (s' : K ⟶ J) (d : K ⟶ D)
    (hr : r ≫ s = c ≫ b) (hn : f ≫ c = c' ≫ f')
    (hb : f' ≫ b = p ≫ u ≫ b') (hp : c' ≫ p = q ≫ v ≫ t)
    (hw : w ≫ t' = t ≫ u) (hv : r' ≫ s' = v ≫ w)
    (hd : d ≫ s = s' ≫ t' ≫ b') : f ≫ r = q ≫ r' ≫ d := by
  apply (cancel_mono s).1
  simp only [Category.assoc]
  rw [hr, reassoc_of% hn, hb]
  rw [reassoc_of% hp, ← reassoc_of% hw, ← reassoc_of% hv, ← hd]

private theorem beta_open_factor
    (P : WeilConjectures.PurityFiniteSetting.{u})
    {X Y X₁ Y₁ X₀ Y₀ X₁₀ Y₁₀ T T₁ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [X₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₁ ↘ Spec (.of P.field.k))]
    [Y₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₁ ↘ Spec (.of P.field.k))]
    [X₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₀ ↘ Spec (.of P.field.k))]
    [Y₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₀ ↘ Spec (.of P.field.k))]
    [X₁₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₁₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₁₀ ↘ Spec (.of P.field.k))]
    [Y₁₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₁₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₁₀ ↘ Spec (.of P.field.k))]
    [T.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (T ↘ Spec (.of P.field.k))]
    [QuasiCompact (T ↘ Spec (.of P.field.k))]
    [T₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (T₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (T₁ ↘ Spec (.of P.field.k))]
    (h : X ⟶ Y) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (dh : ℕ) [SmoothOfRelativeDimension dh h]
    (h₁ : X₁ ⟶ Y₁) [h₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₁] [LocallyOfFiniteType h₁] [QuasiCompact h₁]
    (dh₁ : ℕ) [SmoothOfRelativeDimension dh₁ h₁]
    (h₀ : X₀ ⟶ Y₀) [h₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₀] [LocallyOfFiniteType h₀] [QuasiCompact h₀]
    (h₁₀ : X₁₀ ⟶ Y₁₀) [h₁₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₁₀] [LocallyOfFiniteType h₁₀] [QuasiCompact h₁₀]
    (u : X₁ ⟶ X) [u.IsOver (Spec (.of P.field.k))]
    [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    (v : Y₁ ⟶ Y) [v.IsOver (Spec (.of P.field.k))]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (u₀ : X₁₀ ⟶ X₀) [u₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated u₀] [LocallyOfFiniteType u₀] [QuasiCompact u₀]
    (v₀ : Y₁₀ ⟶ Y₀) [v₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated v₀] [LocallyOfFiniteType v₀] [QuasiCompact v₀]
    (a : X₀ ⟶ X) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [Etale a]
    (b : Y₀ ⟶ Y) [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    [Etale b]
    (a₁ : X₁₀ ⟶ X₁) [a₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated a₁] [LocallyOfFiniteType a₁] [QuasiCompact a₁]
    [Etale a₁]
    (b₁ : Y₁₀ ⟶ Y₁) [b₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated b₁] [LocallyOfFiniteType b₁] [QuasiCompact b₁]
    [Etale b₁]
    (i : T ⟶ X) [i.IsOver (Spec (.of P.field.k))]
    [IsSeparated i] [LocallyOfFiniteType i] [QuasiCompact i]
    [Etale i]
    (t : T ⟶ Y₀) [t.IsOver (Spec (.of P.field.k))]
    [IsSeparated t] [LocallyOfFiniteType t] [QuasiCompact t]
    (dt : ℕ) [SmoothOfRelativeDimension dt t]
    (i₁ : T₁ ⟶ X₁) [i₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated i₁] [LocallyOfFiniteType i₁] [QuasiCompact i₁]
    [Etale i₁]
    (t₁ : T₁ ⟶ Y₁₀) [t₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated t₁] [LocallyOfFiniteType t₁] [QuasiCompact t₁]
    (dt₁ : ℕ) [SmoothOfRelativeDimension dt₁ t₁]
    (j : X₀ ⟶ T) [j.IsOver (Spec (.of P.field.k))]
    [IsSeparated j] [LocallyOfFiniteType j] [QuasiCompact j]
    [Etale j]
    (j₁ : X₁₀ ⟶ T₁) [j₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated j₁] [LocallyOfFiniteType j₁] [QuasiCompact j₁]
    [Etale j₁]
    (U : T₁ ⟶ T) [U.IsOver (Spec (.of P.field.k))]
    [IsSeparated U] [LocallyOfFiniteType U] [QuasiCompact U]
    (sq : IsPullback u h₁ h v) (sq₀ : IsPullback u₀ h₁₀ h₀ v₀)
    (sqh : CommSq a h₀ h b) (sqh₁ : CommSq a₁ h₁₀ h₁ b₁)
    (squ : CommSq a₁ u₀ u a) (sqv : CommSq b₁ v₀ v b)
    (sqtarget : IsPullback i t h b) (sqtarget₁ : IsPullback i₁ t₁ h₁ b₁)
    (sqbar : IsPullback U t₁ t v₀) (sqsrc : IsPullback u₀ j₁ j U)
    (sqU : CommSq i₁ U u i)
    (hji : j ≫ i = a) (hjt : j ≫ t = h₀)
    (hji₁ : j₁ ≫ i₁ = a₁) (hjt₁ : j₁ ≫ t₁ = h₁₀) :
    (pull P a₁).map (beta P h h₁ v u sq) ≫
        (openRestriction P h₁ h₁₀ a₁ b₁ sqh₁).hom =
      (openSquarePull P a₁ u₀ u a squ).hom.app (omega P h) ≫
        (pull P u₀).map (openRestriction P h h₀ a b sqh).hom ≫
        beta P h₀ h₁₀ v₀ u₀ sq₀ := by
  let C := ModuleCat.{u + 1} P.Coefficient
  let := SmoothOfRelativeDimension.smooth dh h
  let := SmoothOfRelativeDimension.smooth dh₁ h₁
  let := SmoothOfRelativeDimension.smooth dt t
  let := SmoothOfRelativeDimension.smooth dt₁ t₁
  have hf₀ := openRestriction_source_factor P j i h dh t b a h₀
    hji hjt sqtarget.toCommSq sqh
  have hf₁ := openRestriction_source_factor P j₁ i₁ h₁ dh₁ t₁ b₁ a₁ h₁₀
    hji₁ hjt₁ sqtarget₁.toCommSq sqh₁
  erw [openRestriction_cartesian P h t i b sqtarget] at hf₀
  erw [openRestriction_cartesian P h₁ t₁ i₁ b₁ sqtarget₁] at hf₁
  have hb := source_beta_eq P t dt t₁ dt₁ v₀ U j j₁ u₀
    h₀ h₁₀ hjt hjt₁ sqbar sqsrc sq₀
  have hr := beta_rectangle P h h₁ u v i t i₁ t₁ b b₁ U v₀
    sq sqtarget sqtarget₁ sqbar sqU sqv
  have hn := (Etale.leftDerivedUpperStarComp C j₁ i₁ a₁ hji₁.symm).hom.naturality
    (beta P h h₁ v u sq)
  have hn' := (openSquarePull P u₀ j₁ j U sqsrc.toCommSq).hom.naturality
    (beta P h t b i sqtarget)
  simp only [Functor.comp_map] at hn hn'
  have hmhr :
      (pull P j₁).map ((pull P i₁).map (beta P h h₁ v u sq)) ≫
        (pull P j₁).map (beta P h₁ t₁ b₁ i₁ sqtarget₁) =
      (pull P j₁).map ((openSquarePull P i₁ U u i sqU).hom.app (omega P h)) ≫
        (pull P j₁).map ((pull P U).map (beta P h t b i sqtarget)) ≫
        (pull P j₁).map (beta P t t₁ v₀ U sqbar) := by
    calc
      _ = (pull P j₁).map
          ((pull P i₁).map (beta P h h₁ v u sq) ≫
            beta P h₁ t₁ b₁ i₁ sqtarget₁) := (Functor.map_comp _ _ _).symm
      _ = _ := congrArg (pull P j₁).map hr
      _ = _ := (Functor.map_comp _ _ _).trans
        (congrArg (_ ≫ ·) (Functor.map_comp _ _ _))
  have hmf₀ :
      (pull P u₀).map (openRestriction P h h₀ a b sqh).hom ≫
        (pull P u₀).map ((sourceCompEq P j t h₀ hjt).hom.app
          (coefficientUnit C Y₀)) =
      (pull P u₀).map ((Etale.leftDerivedUpperStarComp C j i a hji.symm).hom.app
        (omega P h)) ≫
        (pull P u₀).map ((pull P j).map (beta P h t b i sqtarget)) := by
    exact (Functor.map_comp _ _ _).symm.trans
      ((congrArg (pull P u₀).map hf₀).trans (Functor.map_comp _ _ _))
  exact pasting_word
    ((pull P a₁).map (beta P h h₁ v u sq))
    (openRestriction P h₁ h₁₀ a₁ b₁ sqh₁).hom
    ((sourceCompEq P j₁ t₁ h₁₀ hjt₁).hom.app (coefficientUnit C Y₁₀))
    ((Etale.leftDerivedUpperStarComp C j₁ i₁ a₁ hji₁.symm).hom.app (omega P h₁))
    ((pull P j₁).map (beta P h₁ t₁ b₁ i₁ sqtarget₁))
    ((Etale.leftDerivedUpperStarComp C j₁ i₁ a₁ hji₁.symm).hom.app
      ((pull P u).obj (omega P h)))
    ((pull P j₁).map ((pull P i₁).map (beta P h h₁ v u sq)))
    ((pull P j₁).map ((openSquarePull P i₁ U u i sqU).hom.app (omega P h)))
    ((pull P j₁).map ((pull P U).map (beta P h t b i sqtarget)))
    ((pull P j₁).map (beta P t t₁ v₀ U sqbar))
    ((openSquarePull P a₁ u₀ u a squ).hom.app (omega P h))
    ((pull P u₀).map ((Etale.leftDerivedUpperStarComp C j i a hji.symm).hom.app
      (omega P h)))
    ((openSquarePull P u₀ j₁ j U sqsrc.toCommSq).hom.app
      ((pull P i).obj (omega P h)))
    ((pull P u₀).map ((pull P j).map (beta P h t b i sqtarget)))
    ((openSquarePull P u₀ j₁ j U sqsrc.toCommSq).hom.app (omega P t))
    ((pull P u₀).map (openRestriction P h h₀ a b sqh).hom)
    ((pull P u₀).map ((sourceCompEq P j t h₀ hjt).hom.app
      (coefficientUnit C Y₀)))
    (beta P h₀ h₁₀ v₀ u₀ sq₀)
    hf₁ hn hmhr
    (pull_square_grid P u i i₁ U j j₁ u₀ a a₁ hji hji₁
      sqU sqsrc.toCommSq squ (omega P h)) hn' hmf₀ hb

private def bifunctorMap {D : Type*} [Category* D] (Bif : D ⥤ D ⥤ D)
    {A A' B B' : D} (f : A ⟶ A') (g : B ⟶ B') :
    (Bif.obj A).obj B ⟶ (Bif.obj A').obj B' :=
  (Bif.map f).app B ≫ (Bif.obj A').map g

private theorem bifunctorMap_comp {D : Type*} [Category* D] (Bif : D ⥤ D ⥤ D)
    {A A' A'' B B' B'' : D} (f : A ⟶ A') (g : B ⟶ B')
    (f' : A' ⟶ A'') (g' : B' ⟶ B'') :
    bifunctorMap Bif f g ≫ bifunctorMap Bif f' g' =
      bifunctorMap Bif (f ≫ f') (g ≫ g') := by
  simp only [bifunctorMap, Category.assoc, Functor.map_comp, NatTrans.comp_app]
  rw [(Bif.map f').naturality_assoc g]

private theorem bifunctorMap_id_left {D : Type*} [Category* D] (Bif : D ⥤ D ⥤ D)
    (A : D) {B B' : D} (g : B ⟶ B') :
    bifunctorMap Bif (𝟙 A) g = (Bif.obj A).map g := by
  simp only [bifunctorMap, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

private theorem bifunctor_path
    {C D : Type*} [Category* C] [Category* D]
    (Bif : D ⥤ D ⥤ D) (F : C ⥤ D)
    {A' A B' B P' P Q' Z : D} {M N N' N'' : C}
    (e₀ : A' ⟶ A) (e₀inv : A ⟶ A') (p : P' ⟶ P) (pinv : P ⟶ P')
    (he : e₀ ≫ e₀inv = 𝟙 A') (hp : p ≫ pinv = 𝟙 P')
    (J : A' ⟶ B') (T : B' ⟶ B)
    (j : P' ⟶ Q') (q : Q' ⟶ F.obj M) (e : M ⟶ N)
    (k : N ⟶ N') (t : N' ⟶ N'') (z : (Bif.obj B).obj (F.obj N'') ⟶ Z) :
    bifunctorMap Bif J j ≫ bifunctorMap Bif T q ≫ (Bif.obj B).map (F.map e) ≫
      bifunctorMap Bif (𝟙 B) (F.map k) ≫ bifunctorMap Bif (𝟙 B) (F.map t) ≫ z =
    bifunctorMap Bif e₀ p ≫
      bifunctorMap Bif (e₀inv ≫ J ≫ T) (pinv ≫ j ≫ q ≫ F.map (e ≫ k ≫ t)) ≫ z := by
  rw [← bifunctorMap_id_left Bif B (F.map e)]
  simp only [← Category.assoc, bifunctorMap_comp]
  simp only [Category.assoc, Functor.map_comp, reassoc_of% he, reassoc_of% hp,
    Category.comp_id]

private theorem derived_tensor_path
    (R : Type (u + 1)) [CommRing R] (X : Scheme.{u})
    {C : Type*} [Category* C]
    (F : C ⥤ Etale.DerivedCategoryModule R X)
    {A' A B' B P' P Q' Z : Etale.DerivedCategoryModule R X} {M N N' N'' : C}
    (e₀ : A' ⟶ A) (e₀inv : A ⟶ A') (p : P' ⟶ P) (pinv : P ⟶ P')
    (he : e₀ ≫ e₀inv = 𝟙 A') (hp : p ≫ pinv = 𝟙 P')
    (J : A' ⟶ B') (T : B' ⟶ B)
    (j : P' ⟶ Q') (q : Q' ⟶ F.obj M) (e : M ⟶ N)
    (k : N ⟶ N') (t : N' ⟶ N'') (z : ((Etale.derivedTensor (ModuleCat.{u + 1} R) X).obj B).obj
      (F.obj N'') ⟶ Z) :
    Etale.derivedTensorHom (ModuleCat.{u + 1} R) J j ≫
      Etale.derivedTensorHom (ModuleCat.{u + 1} R) T q ≫
      ((Etale.derivedTensor (ModuleCat.{u + 1} R) X).obj B).map (F.map e) ≫
      Etale.derivedTensorHom (ModuleCat.{u + 1} R) (𝟙 B) (F.map k) ≫
      Etale.derivedTensorHom (ModuleCat.{u + 1} R) (𝟙 B) (F.map t) ≫ z =
    Etale.derivedTensorHom (ModuleCat.{u + 1} R) e₀ p ≫
      Etale.derivedTensorHom (ModuleCat.{u + 1} R) (e₀inv ≫ J ≫ T)
        (pinv ≫ j ≫ q ≫ F.map (e ≫ k ≫ t)) ≫ z := by
  simpa only [bifunctorMap, Etale.derivedTensorHom] using
    bifunctor_path (Etale.derivedTensor (ModuleCat.{u + 1} R) X) F
      e₀ e₀inv p pinv he hp J T j q e k t z

private theorem cube_factorization
    {C : Type*} [Category C] [HasPullbacks C]
    {X Y X₁ Y₁ X₀ Y₀ X₁₀ Y₁₀ : C}
    (h : X ⟶ Y) (h₁ : X₁ ⟶ Y₁) (u : X₁ ⟶ X) (v : Y₁ ⟶ Y)
    (h₀ : X₀ ⟶ Y₀) (h₁₀ : X₁₀ ⟶ Y₁₀) (u₀ : X₁₀ ⟶ X₀) (v₀ : Y₁₀ ⟶ Y₀)
    (a : X₀ ⟶ X) (b : Y₀ ⟶ Y) (a₁ : X₁₀ ⟶ X₁) (b₁ : Y₁₀ ⟶ Y₁)
    (sq : IsPullback u h₁ h v) (sq₀ : IsPullback u₀ h₁₀ h₀ v₀)
    (sqh : CommSq a h₀ h b) (sqh₁ : CommSq a₁ h₁₀ h₁ b₁)
    (squ : CommSq a₁ u₀ u a) (sqv : CommSq b₁ v₀ v b) :
    let j := pullback.lift a h₀ sqh.w
    let j₁ := pullback.lift a₁ h₁₀ sqh₁.w
    ∃ U : pullback h₁ b₁ ⟶ pullback h b,
      U ≫ pullback.fst h b = pullback.fst h₁ b₁ ≫ u ∧
      U ≫ pullback.snd h b = pullback.snd h₁ b₁ ≫ v₀ ∧
      IsPullback U (pullback.snd h₁ b₁) (pullback.snd h b) v₀ ∧
      IsPullback u₀ j₁ j U := by
  dsimp only
  have hw : (pullback.fst h₁ b₁ ≫ u) ≫ h =
      (pullback.snd h₁ b₁ ≫ v₀) ≫ b := by
    rw [Category.assoc, sq.w, ← Category.assoc,
      pullback.condition, Category.assoc, sqv.w, Category.assoc]
  let U := pullback.lift (pullback.fst h₁ b₁ ≫ u)
    (pullback.snd h₁ b₁ ≫ v₀) hw
  have hU₁ : U ≫ pullback.fst h b = pullback.fst h₁ b₁ ≫ u := by simp [U]
  have hU₂ : U ≫ pullback.snd h b = pullback.snd h₁ b₁ ≫ v₀ := by simp [U]
  have houter : IsPullback (U ≫ pullback.fst h b) (pullback.snd h₁ b₁)
      h (v₀ ≫ b) := by
    rw [hU₁, ← sqv.w]
    exact (IsPullback.of_hasPullback h₁ b₁).paste_horiz sq
  have hbar : IsPullback U (pullback.snd h₁ b₁) (pullback.snd h b) v₀ :=
    houter.of_right hU₂ (IsPullback.of_hasPullback h b)
  have hj : u₀ ≫ pullback.lift a h₀ sqh.w =
      pullback.lift a₁ h₁₀ sqh₁.w ≫ U := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hU₁, pullback.lift_fst, pullback.lift_fst_assoc]
      exact squ.w.symm
    · simp only [Category.assoc, hU₂, pullback.lift_snd, pullback.lift_snd_assoc]
      exact sq₀.w
  have hsrc : IsPullback u₀ (pullback.lift a₁ h₁₀ sqh₁.w)
      (pullback.lift a h₀ sqh.w) U := by
    apply IsPullback.of_bot (t := hbar) (p := hj)
    simpa only [pullback.lift_snd] using sq₀
  exact ⟨U, hU₁, hU₂, hbar, hsrc⟩

private theorem cancel_precomposition
    {D : Type*} [Category* D] {A B C : D}
    (q : A ⟶ B) (r : B ⟶ A) (hi : r ≫ q = 𝟙 B)
    {f g : B ⟶ C} (h : q ≫ f = q ≫ g) : f = g := by
  calc
    f = r ≫ (q ≫ f) := by rw [← Category.assoc, hi, Category.id_comp]
    _ = r ≫ (q ≫ g) := by rw [h]
    _ = g := by rw [← Category.assoc, hi, Category.id_comp]

private theorem sigma_path_word
    {C : Type*} [Category* C]
    {A B D E F G H P Q R S U Z : C}
    (s₀ : A ⟶ B) (s₁ : P ⟶ E) (s₂ : Q ⟶ F) (s₃ : R ⟶ G) (s₄ : S ⟶ Z)
    (a : B ⟶ H) (b : H ⟶ D) (t : D ⟶ Z)
    (c₁ : B ⟶ E) (c₂ : E ⟶ F) (c₃ : F ⟶ G) (c₄ : G ⟶ D)
    (u₁ : A ⟶ P) (u₂ : P ⟶ U) (u₂' : U ⟶ Q) (u₃ : Q ⟶ R) (u₄ : R ⟶ S)
    (hp : a ≫ b = c₁ ≫ c₂ ≫ c₃ ≫ c₄)
    (h₁ : s₀ ≫ c₁ = u₁ ≫ s₁) (h₂ : s₁ ≫ c₂ = u₂ ≫ u₂' ≫ s₂)
    (h₃ : s₂ ≫ c₃ = u₃ ≫ s₃) (h₄ : s₃ ≫ c₄ ≫ t = u₄ ≫ s₄) :
    s₀ ≫ a ≫ b ≫ t = u₁ ≫ u₂ ≫ u₂' ≫ u₃ ≫ u₄ ≫ s₄ := by
  rw [reassoc_of% hp, reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, h₄]

private theorem sigma_open_restriction
    (P : WeilConjectures.PurityFiniteSetting.{u}) :
    ∀
    {X Y Z X₀ Y₀ Z₀ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [X₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₀ ↘ Spec (.of P.field.k))]
    [Y₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₀ ↘ Spec (.of P.field.k))]
    [Z₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z₀ ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (df : ℕ) [SmoothOfRelativeDimension df f]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (dg : ℕ) [SmoothOfRelativeDimension dg g]
    (f₀ : X₀ ⟶ Y₀) [f₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated f₀] [LocallyOfFiniteType f₀] [QuasiCompact f₀]
    (df₀ : ℕ) [SmoothOfRelativeDimension df₀ f₀]
    (g₀ : Y₀ ⟶ Z₀) [g₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated g₀] [LocallyOfFiniteType g₀] [QuasiCompact g₀]
    (dg₀ : ℕ) [SmoothOfRelativeDimension dg₀ g₀]
    (a : X₀ ⟶ X) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [IsOpenImmersion a]
    (b : Y₀ ⟶ Y) [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    [IsOpenImmersion b]
    (c : Z₀ ⟶ Z) [c.IsOver (Spec (.of P.field.k))]
    [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
    [IsOpenImmersion c]
    (sqf : CommSq a f₀ f b) (sqg : CommSq b g₀ g c),
    (pull P a).map ((FiniteEtaleNormalization.sigma P.Coefficient
      f g (cf := compactification P f)
      (cg := compactification P g)
      (cfg := compactification P (f ≫ g))
      (comp P f g))) ≫
      (((sourceEtale P a (f ≫ g)).symm ≪≫
        (FiniteEtaleNormalization.congr P (a ≫ (f ≫ g)) ((f₀ ≫ g₀) ≫ c) ((sqf.vert_comp sqg)).w).app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (comp P (f₀ ≫ g₀) c).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (exceptional P (f₀ ≫ g₀)).mapIso (eta P c))).hom =
    (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) a
      (omega P f) ((pull P f).obj (omega P g))).hom ≫
    Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient)
      (((sourceEtale P a f).symm ≪≫
        (FiniteEtaleNormalization.congr P (a ≫ f) (f₀ ≫ b) (sqf).w).app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (comp P f₀ b).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (exceptional P f₀).mapIso (eta P b))).hom
      ((((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          a f (f₀ ≫ b) (sqf).w.symm).symm ≪≫
        Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f₀ b)).hom.app (omega P
        g) ≫
        (pull P f₀).map (((sourceEtale P b g).symm ≪≫
        (FiniteEtaleNormalization.congr P (b ≫ g) (g₀ ≫ c) (sqg).w).app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (comp P g₀ c).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (exceptional P g₀).mapIso (eta P c))).hom) ≫
      (FiniteEtaleNormalization.sigma P.Coefficient
      f₀ g₀ (cf := compactification P f₀)
      (cg := compactification P g₀)
      (cfg := compactification P (f₀ ≫ g₀))
      (comp P f₀ g₀)) := by
  intro X Y Z X₀ Y₀ Z₀ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    f _ _ _ _ df _ g _ _ _ _ dg _ f₀ _ _ _ _ df₀ _ g₀ _ _ _ _ dg₀ _
    a _ _ _ _ _ b _ _ _ _ _ c _ _ _ _ _ sqf sqg
  let C := ModuleCat.{u + 1} P.Coefficient
  have hsrc := (dualizing_cocycle_source_etale P).2 a 0 f df g dg
  have heq₁ := sigma_eq_left P (a ≫ f) g (f₀ ≫ b) sqf.w
  have hmid := sigma_middle_etale P f₀ df₀ b g dg
  have heq₂ := sigma_eq_right P f₀ (b ≫ g) (g₀ ≫ c) sqg.w
  have htar := sigma_target_restriction P f₀ g₀ c
  let Hhom := Etale.derivedTensorHom C (sourceEtale P a f).hom
    ((Etale.leftDerivedUpperStarComp C a f).hom.app (omega P g)) ≫
    (Etale.leftDerivedUpperStarTensorIso C a (omega P f)
      ((pull P f).obj (omega P g))).inv
  let Hinv := (Etale.leftDerivedUpperStarTensorIso C a (omega P f)
    ((pull P f).obj (omega P g))).hom ≫
    Etale.derivedTensorHom C (sourceEtale P a f).inv
      ((Etale.leftDerivedUpperStarComp C a f).inv.app (omega P g))
  have hInv : Hinv ≫ Hhom = 𝟙 _ := by
    simp only [Hinv, Hhom, Category.assoc, Etale.derivedTensorHom_comp_assoc,
      Iso.inv_hom_id, Iso.inv_hom_id_app]
    erw [Etale.derivedTensorHom_id, Category.id_comp, Iso.hom_inv_id]
  apply cancel_precomposition Hhom Hinv hInv
  simp only [Hhom, C, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  rw [← reassoc_of% hsrc]
  simp only [Iso.app_hom, Functor.mapIso_hom,
    Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc]
  have hpath :
      (FiniteEtaleNormalization.congr P ((a ≫ f) ≫ g) (a ≫ (f ≫ g))
        (Category.assoc a f g)).hom.app (coefficientUnit C Z) ≫
      (FiniteEtaleNormalization.congr P (a ≫ (f ≫ g)) ((f₀ ≫ g₀) ≫ c)
        (sqf.vert_comp sqg).w).hom.app (coefficientUnit C Z) =
      (FiniteEtaleNormalization.congr P ((a ≫ f) ≫ g) ((f₀ ≫ b) ≫ g)
        (by rw [sqf.w])).hom.app (coefficientUnit C Z) ≫
      (FiniteEtaleNormalization.congr P ((f₀ ≫ b) ≫ g) (f₀ ≫ (b ≫ g))
        (Category.assoc f₀ b g)).hom.app (coefficientUnit C Z) ≫
      (FiniteEtaleNormalization.congr P (f₀ ≫ (b ≫ g)) (f₀ ≫ (g₀ ≫ c))
        (by rw [sqg.w])).hom.app (coefficientUnit C Z) ≫
      (FiniteEtaleNormalization.congr P (f₀ ≫ (g₀ ≫ c)) ((f₀ ≫ g₀) ≫ c)
        (Category.assoc f₀ g₀ c).symm).hom.app (coefficientUnit C Z) := by
    simp only [exceptional_congr_trans_app]
  have hchain := sigma_path_word
    (sigmaMap P (a ≫ f) g) (sigmaMap P (f₀ ≫ b) g)
    (sigmaMap P f₀ (b ≫ g)) (sigmaMap P f₀ (g₀ ≫ c)) (sigmaMap P f₀ g₀)
    ((FiniteEtaleNormalization.congr P ((a ≫ f) ≫ g) (a ≫ (f ≫ g))
      (Category.assoc a f g)).hom.app (coefficientUnit C Z))
    ((FiniteEtaleNormalization.congr P (a ≫ (f ≫ g)) ((f₀ ≫ g₀) ≫ c)
      (sqf.vert_comp sqg).w).hom.app (coefficientUnit C Z))
    ((comp P (f₀ ≫ g₀) c).hom.app (coefficientUnit C Z) ≫
      (exceptional P (f₀ ≫ g₀)).map (eta P c).hom)
    ((FiniteEtaleNormalization.congr P ((a ≫ f) ≫ g) ((f₀ ≫ b) ≫ g)
      (by rw [sqf.w])).hom.app (coefficientUnit C Z))
    ((FiniteEtaleNormalization.congr P ((f₀ ≫ b) ≫ g) (f₀ ≫ (b ≫ g))
      (Category.assoc f₀ b g)).hom.app (coefficientUnit C Z))
    ((FiniteEtaleNormalization.congr P (f₀ ≫ (b ≫ g)) (f₀ ≫ (g₀ ≫ c))
      (by rw [sqg.w])).hom.app (coefficientUnit C Z))
    ((FiniteEtaleNormalization.congr P (f₀ ≫ (g₀ ≫ c)) ((f₀ ≫ g₀) ≫ c)
      (Category.assoc f₀ g₀ c).symm).hom.app (coefficientUnit C Z))
    (Etale.derivedTensorHom C
      ((FiniteEtaleNormalization.congr P (a ≫ f) (f₀ ≫ b) sqf.w).hom.app
        (coefficientUnit C Y))
      ((pullCongr P (a ≫ f) (f₀ ≫ b) sqf.w).hom.app (omega P g)))
    (Etale.derivedTensorHom C (targetRestriction P f₀ b).hom
      ((Etale.leftDerivedUpperStarComp C f₀ b).hom.app (omega P g)))
    (((Etale.derivedTensor C X₀).obj (omega P f₀)).map
      ((pull P f₀).map (sourceEtale P b g).inv))
    (Etale.derivedTensorHom C (𝟙 (omega P f₀))
      ((pull P f₀).map ((FiniteEtaleNormalization.congr P (b ≫ g) (g₀ ≫ c)
        sqg.w).hom.app (coefficientUnit C Z))))
    (Etale.derivedTensorHom C (𝟙 (omega P f₀))
      ((pull P f₀).map (targetRestriction P g₀ c).hom))
    hpath heq₁ hmid heq₂ htar
  refine hchain.trans ?_
  have hχ := openSquarePull_hom_canonical P a f₀ f b sqf (omega P g)
  simp only [openSquarePull, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app] at hχ ⊢
  erw [hχ]
  have hf := derived_tensor_path P.Coefficient X₀ (pull P f₀)
    (sourceEtale P a f).hom (sourceEtale P a f).inv
    ((Etale.leftDerivedUpperStarComp C a f).hom.app (omega P g))
    ((Etale.leftDerivedUpperStarComp C a f).inv.app (omega P g))
    (Iso.hom_inv_id (sourceEtale P a f))
    (Iso.hom_inv_id_app (Etale.leftDerivedUpperStarComp C a f) (omega P g))
    ((FiniteEtaleNormalization.congr P (a ≫ f) (f₀ ≫ b) sqf.w).hom.app
      (coefficientUnit C Y)) (targetRestriction P f₀ b).hom
    ((pullCongr P (a ≫ f) (f₀ ≫ b) sqf.w).hom.app (omega P g))
    ((Etale.leftDerivedUpperStarComp C f₀ b).hom.app (omega P g))
    (sourceEtale P b g).inv
    ((FiniteEtaleNormalization.congr P (b ≫ g) (g₀ ≫ c) sqg.w).hom.app
      (coefficientUnit C Z))
    (targetRestriction P g₀ c).hom (sigmaMap P f₀ g₀)
  -- Keep the concrete derived functors folded during this normalization.
  simpa only [targetRestriction_hom, Category.assoc, Functor.map_comp, C] using hf

private theorem beta_open_restriction
    (P : WeilConjectures.PurityFiniteSetting.{u}) :
    ∀
    {X Y X₁ Y₁ X₀ Y₀ X₁₀ Y₁₀ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [X₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₁ ↘ Spec (.of P.field.k))]
    [Y₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₁ ↘ Spec (.of P.field.k))]
    [X₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₀ ↘ Spec (.of P.field.k))]
    [Y₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₀ ↘ Spec (.of P.field.k))]
    [X₁₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₁₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₁₀ ↘ Spec (.of P.field.k))]
    [Y₁₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₁₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₁₀ ↘ Spec (.of P.field.k))]
    (h : X ⟶ Y) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (dh : ℕ) [SmoothOfRelativeDimension dh h]
    (h₁ : X₁ ⟶ Y₁) [h₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₁] [LocallyOfFiniteType h₁] [QuasiCompact h₁]
    (dh₁ : ℕ) [SmoothOfRelativeDimension dh₁ h₁]
    (v : Y₁ ⟶ Y) [v.IsOver (Spec (.of P.field.k))]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (u : X₁ ⟶ X) [u.IsOver (Spec (.of P.field.k))]
    [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    (h₀ : X₀ ⟶ Y₀) [h₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₀] [LocallyOfFiniteType h₀] [QuasiCompact h₀]
    (dh₀ : ℕ) [SmoothOfRelativeDimension dh₀ h₀]
    (h₁₀ : X₁₀ ⟶ Y₁₀) [h₁₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₁₀] [LocallyOfFiniteType h₁₀] [QuasiCompact h₁₀]
    (dh₁₀ : ℕ) [SmoothOfRelativeDimension dh₁₀ h₁₀]
    (v₀ : Y₁₀ ⟶ Y₀) [v₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated v₀] [LocallyOfFiniteType v₀] [QuasiCompact v₀]
    (u₀ : X₁₀ ⟶ X₀) [u₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated u₀] [LocallyOfFiniteType u₀] [QuasiCompact u₀]
    (a : X₀ ⟶ X) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [IsOpenImmersion a]
    (b : Y₀ ⟶ Y) [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    [IsOpenImmersion b]
    (a₁ : X₁₀ ⟶ X₁) [a₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated a₁] [LocallyOfFiniteType a₁] [QuasiCompact a₁]
    [IsOpenImmersion a₁]
    (b₁ : Y₁₀ ⟶ Y₁) [b₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated b₁] [LocallyOfFiniteType b₁] [QuasiCompact b₁]
    [IsOpenImmersion b₁]
    (sq : IsPullback u h₁ h v) (sq₀ : IsPullback u₀ h₁₀ h₀ v₀)
    (sqh : CommSq a h₀ h b) (sqh₁ : CommSq a₁ h₁₀ h₁ b₁)
    (squ : CommSq a₁ u₀ u a) (_sqv : CommSq b₁ v₀ v b),
    (pull P a₁).map (beta P h h₁ v u sq) ≫
      (((sourceEtale P a₁ h₁).symm ≪≫
        (FiniteEtaleNormalization.congr P (a₁ ≫ h₁) (h₁₀ ≫ b₁) (sqh₁).w).app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (comp P h₁₀ b₁).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (exceptional P h₁₀).mapIso (eta P b₁))).hom =
    (((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          a₁ u (u₀ ≫ a) (squ).w.symm).symm ≪≫
        Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) u₀ a)).hom.app (omega P
        h) ≫
      (pull P u₀).map (((sourceEtale P a h).symm ≪≫
        (FiniteEtaleNormalization.congr P (a ≫ h) (h₀ ≫ b) (sqh).w).app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (comp P h₀ b).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (exceptional P h₀).mapIso (eta P b))).hom ≫
      beta P h₀ h₁₀ v₀ u₀ sq₀ := by
  intro X Y X₁ Y₁ X₀ Y₀ X₁₀ Y₁₀ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ h _ _ _ _ dh _ h₁ _ _ _ _ dh₁ _ v _ _ _ _ u _ _ _ _
    h₀ _ _ _ _ dh₀ _ h₁₀ _ _ _ _ dh₁₀ _ v₀ _ _ _ _ u₀ _ _ _ _
    a _ _ _ _ _ b _ _ _ _ _ a₁ _ _ _ _ _ b₁ _ _ _ _ _
    sq sq₀ sqh sqh₁ squ sqv
  let F := Spec (.of P.field.k)
  let T := pullback h b
  let T₁ := pullback h₁ b₁
  let i : T ⟶ X := pullback.fst h b
  let t : T ⟶ Y₀ := pullback.snd h b
  let i₁ : T₁ ⟶ X₁ := pullback.fst h₁ b₁
  let t₁ : T₁ ⟶ Y₁₀ := pullback.snd h₁ b₁
  let j : X₀ ⟶ T := pullback.lift a h₀ sqh.w
  let j₁ : X₁₀ ⟶ T₁ := pullback.lift a₁ h₁₀ sqh₁.w
  have hji : j ≫ i = a := pullback.lift_fst _ _ _
  have hjt : j ≫ t = h₀ := pullback.lift_snd _ _ _
  have hji₁ : j₁ ≫ i₁ = a₁ := pullback.lift_fst _ _ _
  have hjt₁ : j₁ ≫ t₁ = h₁₀ := pullback.lift_snd _ _ _
  obtain ⟨U, hU₁, hU₂, sqbar, sqsrc⟩ := cube_factorization h h₁ u v
    h₀ h₁₀ u₀ v₀ a b a₁ b₁ sq sq₀ sqh sqh₁ squ sqv
  let : T.Over F := ⟨t ≫ (Y₀ ↘ F)⟩
  let : T₁.Over F := ⟨t₁ ≫ (Y₁₀ ↘ F)⟩
  let : t.IsOver F := ⟨rfl⟩
  let : t₁.IsOver F := ⟨rfl⟩
  let : LocallyOfFiniteType (T ↘ F) :=
    inferInstanceAs (LocallyOfFiniteType (t ≫ (Y₀ ↘ F)))
  let : QuasiCompact (T ↘ F) := inferInstanceAs (QuasiCompact (t ≫ (Y₀ ↘ F)))
  let : LocallyOfFiniteType (T₁ ↘ F) :=
    inferInstanceAs (LocallyOfFiniteType (t₁ ≫ (Y₁₀ ↘ F)))
  let : QuasiCompact (T₁ ↘ F) := inferInstanceAs (QuasiCompact (t₁ ≫ (Y₁₀ ↘ F)))
  let : i.IsOver F := ⟨by
    change i ≫ (X ↘ F) = t ≫ (Y₀ ↘ F)
    rw [← comp_over h, ← Category.assoc, pullback.condition, Category.assoc, comp_over b]⟩
  let : i₁.IsOver F := ⟨by
    change i₁ ≫ (X₁ ↘ F) = t₁ ≫ (Y₁₀ ↘ F)
    rw [← comp_over h₁, ← Category.assoc, pullback.condition, Category.assoc, comp_over b₁]⟩
  let : j.IsOver F := ⟨by
    change j ≫ t ≫ (Y₀ ↘ F) = X₀ ↘ F
    rw [← Category.assoc, hjt, comp_over h₀]⟩
  let : j₁.IsOver F := ⟨by
    change j₁ ≫ t₁ ≫ (Y₁₀ ↘ F) = X₁₀ ↘ F
    rw [← Category.assoc, hjt₁, comp_over h₁₀]⟩
  let : IsOpenImmersion (j ≫ i) := by rw [hji]; infer_instance
  let : IsOpenImmersion (j₁ ≫ i₁) := by rw [hji₁]; infer_instance
  let : IsOpenImmersion j := IsOpenImmersion.of_comp j i
  let : IsOpenImmersion j₁ := IsOpenImmersion.of_comp j₁ i₁
  let := fieldSchemeNoetherian P X₀
  let := fieldSchemeNoetherian P X₁₀
  let : QuasiCompact j := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  let : QuasiCompact j₁ := ⟨fun _ _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  let : U.IsOver F := ⟨by
    change U ≫ t ≫ (Y₀ ↘ F) = t₁ ≫ (Y₁₀ ↘ F)
    rw [← Category.assoc, hU₂, Category.assoc, comp_over v₀]⟩
  let : IsSeparated U := MorphismProperty.of_isPullback (P := @IsSeparated)
    sqbar.flip inferInstance
  let : LocallyOfFiniteType U := MorphismProperty.of_isPullback
    (P := @LocallyOfFiniteType) sqbar.flip inferInstance
  let : QuasiCompact U := MorphismProperty.of_isPullback (P := @QuasiCompact)
    sqbar.flip inferInstance
  have hp := beta_open_factor P h dh h₁ dh₁ h₀ h₁₀ u v u₀ v₀ a b a₁ b₁
    i t dh i₁ t₁ dh₁ j j₁ U sq sq₀ sqh sqh₁ squ sqv
    (IsPullback.of_hasPullback h b) (IsPullback.of_hasPullback h₁ b₁)
    sqbar sqsrc ⟨hU₁.symm⟩ hji hjt hji₁ hjt₁
  exact hp

/-- The actual sigma, E and beta maps commute with compatible open restrictions.
The four restriction squares in the beta clause need only commute; only its
front and back base-change squares are assumed Cartesian.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-composition/thm-pur-composition-coherence.proof.md, Step 1;
lem-pur-dualizing-sigma-cocycle-locality, proof Step 6, using Steps 1--5.

Proof: Conjugate compact-support associativity through the specified adjunctions
and retain explicit equations for intermediate scheme composites. Naturality of
rho and its normalized composition law then give the E identity. For sigma,
precompose with the invertible source tensor comparison and use the stated
source-etale cocycle. The cocycle for the middle etale arrow, contracted by eta
using the monoidal pullback unit law, gives middle restriction. Naturality of
the canonical tensor map and its coefficient-unit formula give target
restriction. Tensor bifunctoriality and congruence transitivity combine these
three identities into the displayed sigma equation.

For beta, first identify the restriction comparison of a Cartesian open square
with its beta map, using finite-etale normalization and the same tensor unit
formula. A general open square factors through its target pullback; source
compositor associativity identifies its stated comparison with the pulled-back
Cartesian comparison followed by residual source restriction. Apply this to
both open faces of the cube. Horizontal pullback pasting and cancellation prove
that the induced target square and residual source square are Cartesian.
Smooth tensor base-change pasting, normalized by eta, gives source-etale beta
compatibility. Horizontal exceptional base-change pasting at the unit and
ordinary pullback square coherence then identify both cube routes. Cancel the
residual source isomorphism. Only the two stated cube faces are assumed
Cartesian. All domain conditions follow from finite-type field structures and
constructibility of smooth dualizing complexes; no argument requires a point.
(blueprint: lem-route-dualizing-primitive-open-restriction). -/
theorem dualizing_primitive_open_restriction
    (P : WeilConjectures.PurityFiniteSetting.{u}) :
    (∀
    {X Y Z X₀ Y₀ Z₀ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [X₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₀ ↘ Spec (.of P.field.k))]
    [Y₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₀ ↘ Spec (.of P.field.k))]
    [Z₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z₀ ↘ Spec (.of P.field.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of P.field.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (df : ℕ) [SmoothOfRelativeDimension df f]
    (g : Y ⟶ Z) [g.IsOver (Spec (.of P.field.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (dg : ℕ) [SmoothOfRelativeDimension dg g]
    (f₀ : X₀ ⟶ Y₀) [f₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated f₀] [LocallyOfFiniteType f₀] [QuasiCompact f₀]
    (df₀ : ℕ) [SmoothOfRelativeDimension df₀ f₀]
    (g₀ : Y₀ ⟶ Z₀) [g₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated g₀] [LocallyOfFiniteType g₀] [QuasiCompact g₀]
    (dg₀ : ℕ) [SmoothOfRelativeDimension dg₀ g₀]
    (a : X₀ ⟶ X) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [IsOpenImmersion a]
    (b : Y₀ ⟶ Y) [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    [IsOpenImmersion b]
    (c : Z₀ ⟶ Z) [c.IsOver (Spec (.of P.field.k))]
    [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
    [IsOpenImmersion c]
    (sqf : CommSq a f₀ f b) (sqg : CommSq b g₀ g c),
    (pull P a).map ((FiniteEtaleNormalization.sigma P.Coefficient
      f g (cf := compactification P f)
      (cg := compactification P g)
      (cfg := compactification P (f ≫ g))
      (comp P f g))) ≫
      (((sourceEtale P a (f ≫ g)).symm ≪≫
        (FiniteEtaleNormalization.congr P (a ≫ (f ≫ g)) ((f₀ ≫ g₀) ≫ c) ((sqf.vert_comp sqg)).w).app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (comp P (f₀ ≫ g₀) c).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (exceptional P (f₀ ≫ g₀)).mapIso (eta P c))).hom =
    (Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) a
      (omega P f) ((pull P f).obj (omega P g))).hom ≫
    Etale.derivedTensorHom (ModuleCat.{u + 1} P.Coefficient)
      (((sourceEtale P a f).symm ≪≫
        (FiniteEtaleNormalization.congr P (a ≫ f) (f₀ ≫ b) (sqf).w).app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (comp P f₀ b).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (exceptional P f₀).mapIso (eta P b))).hom
      ((((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          a f (f₀ ≫ b) (sqf).w.symm).symm ≪≫
        Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) f₀ b)).hom.app (omega P
        g) ≫
        (pull P f₀).map (((sourceEtale P b g).symm ≪≫
        (FiniteEtaleNormalization.congr P (b ≫ g) (g₀ ≫ c) (sqg).w).app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (comp P g₀ c).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (exceptional P g₀).mapIso (eta P c))).hom) ≫
      (FiniteEtaleNormalization.sigma P.Coefficient
      f₀ g₀ (cf := compactification P f₀)
      (cg := compactification P g₀)
      (cfg := compactification P (f₀ ≫ g₀))
      (comp P f₀ g₀))) ∧
    (∀
    {X Y Z X₀ Y₀ Z₀ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [Z.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z ↘ Spec (.of P.field.k))]
    [X₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₀ ↘ Spec (.of P.field.k))]
    [Y₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₀ ↘ Spec (.of P.field.k))]
    [Z₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Z₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Z₀ ↘ Spec (.of P.field.k))]
    (e : X ⟶ Y) [e.IsOver (Spec (.of P.field.k))]
    [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    [Etale e]
    (h : Y ⟶ Z) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (dh : ℕ) [SmoothOfRelativeDimension dh h]
    (e₀ : X₀ ⟶ Y₀) [e₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated e₀] [LocallyOfFiniteType e₀] [QuasiCompact e₀]
    [Etale e₀]
    (h₀ : Y₀ ⟶ Z₀) [h₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₀] [LocallyOfFiniteType h₀] [QuasiCompact h₀]
    (dh₀ : ℕ) [SmoothOfRelativeDimension dh₀ h₀]
    (a : X₀ ⟶ X) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [IsOpenImmersion a]
    (b : Y₀ ⟶ Y) [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    [IsOpenImmersion b]
    (c : Z₀ ⟶ Z) [c.IsOver (Spec (.of P.field.k))]
    [IsSeparated c] [LocallyOfFiniteType c] [QuasiCompact c]
    [IsOpenImmersion c]
    (sqe : CommSq a e₀ e b) (sqh : CommSq b h₀ h c),
    (pull P a).map (sourceEtale P e h).hom ≫
      (((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          a e (e₀ ≫ b) (sqe).w.symm).symm ≪≫
        Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) e₀ b)).hom.app (omega P
        h) ≫
      (pull P e₀).map (((sourceEtale P b h).symm ≪≫
        (FiniteEtaleNormalization.congr P (b ≫ h) (h₀ ≫ c) (sqh).w).app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (comp P h₀ c).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (exceptional P h₀).mapIso (eta P c))).hom =
    (((sourceEtale P a (e ≫ h)).symm ≪≫
        (FiniteEtaleNormalization.congr P (a ≫ (e ≫ h)) ((e₀ ≫ h₀) ≫ c) ((sqe.vert_comp sqh)).w).app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (comp P (e₀ ≫ h₀) c).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (exceptional P (e₀ ≫ h₀)).mapIso (eta P c))).hom ≫
      (sourceEtale P e₀ h₀).hom) ∧
    (∀
    {X Y X₁ Y₁ X₀ Y₀ X₁₀ Y₁₀ : Scheme.{u}}
    [X.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of P.field.k))]
    [QuasiCompact (X ↘ Spec (.of P.field.k))]
    [Y.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y ↘ Spec (.of P.field.k))]
    [X₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₁ ↘ Spec (.of P.field.k))]
    [Y₁.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₁ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₁ ↘ Spec (.of P.field.k))]
    [X₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₀ ↘ Spec (.of P.field.k))]
    [Y₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₀ ↘ Spec (.of P.field.k))]
    [X₁₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (X₁₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (X₁₀ ↘ Spec (.of P.field.k))]
    [Y₁₀.Over (Spec (.of P.field.k))]
    [LocallyOfFiniteType (Y₁₀ ↘ Spec (.of P.field.k))]
    [QuasiCompact (Y₁₀ ↘ Spec (.of P.field.k))]
    (h : X ⟶ Y) [h.IsOver (Spec (.of P.field.k))]
    [IsSeparated h] [LocallyOfFiniteType h] [QuasiCompact h]
    (dh : ℕ) [SmoothOfRelativeDimension dh h]
    (h₁ : X₁ ⟶ Y₁) [h₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₁] [LocallyOfFiniteType h₁] [QuasiCompact h₁]
    (dh₁ : ℕ) [SmoothOfRelativeDimension dh₁ h₁]
    (v : Y₁ ⟶ Y) [v.IsOver (Spec (.of P.field.k))]
    [IsSeparated v] [LocallyOfFiniteType v] [QuasiCompact v]
    (u : X₁ ⟶ X) [u.IsOver (Spec (.of P.field.k))]
    [IsSeparated u] [LocallyOfFiniteType u] [QuasiCompact u]
    (h₀ : X₀ ⟶ Y₀) [h₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₀] [LocallyOfFiniteType h₀] [QuasiCompact h₀]
    (dh₀ : ℕ) [SmoothOfRelativeDimension dh₀ h₀]
    (h₁₀ : X₁₀ ⟶ Y₁₀) [h₁₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated h₁₀] [LocallyOfFiniteType h₁₀] [QuasiCompact h₁₀]
    (dh₁₀ : ℕ) [SmoothOfRelativeDimension dh₁₀ h₁₀]
    (v₀ : Y₁₀ ⟶ Y₀) [v₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated v₀] [LocallyOfFiniteType v₀] [QuasiCompact v₀]
    (u₀ : X₁₀ ⟶ X₀) [u₀.IsOver (Spec (.of P.field.k))]
    [IsSeparated u₀] [LocallyOfFiniteType u₀] [QuasiCompact u₀]
    (a : X₀ ⟶ X) [a.IsOver (Spec (.of P.field.k))]
    [IsSeparated a] [LocallyOfFiniteType a] [QuasiCompact a]
    [IsOpenImmersion a]
    (b : Y₀ ⟶ Y) [b.IsOver (Spec (.of P.field.k))]
    [IsSeparated b] [LocallyOfFiniteType b] [QuasiCompact b]
    [IsOpenImmersion b]
    (a₁ : X₁₀ ⟶ X₁) [a₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated a₁] [LocallyOfFiniteType a₁] [QuasiCompact a₁]
    [IsOpenImmersion a₁]
    (b₁ : Y₁₀ ⟶ Y₁) [b₁.IsOver (Spec (.of P.field.k))]
    [IsSeparated b₁] [LocallyOfFiniteType b₁] [QuasiCompact b₁]
    [IsOpenImmersion b₁]
    (sq : IsPullback u h₁ h v) (sq₀ : IsPullback u₀ h₁₀ h₀ v₀)
    (sqh : CommSq a h₀ h b) (sqh₁ : CommSq a₁ h₁₀ h₁ b₁)
    (squ : CommSq a₁ u₀ u a) (_sqv : CommSq b₁ v₀ v b),
    (pull P a₁).map (beta P h h₁ v u sq) ≫
      (((sourceEtale P a₁ h₁).symm ≪≫
        (FiniteEtaleNormalization.congr P (a₁ ≫ h₁) (h₁₀ ≫ b₁) (sqh₁).w).app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (comp P h₁₀ b₁).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (exceptional P h₁₀).mapIso (eta P b₁))).hom =
    (((Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient)
          a₁ u (u₀ ≫ a) (squ).w.symm).symm ≪≫
        Etale.leftDerivedUpperStarComp (ModuleCat.{u + 1} P.Coefficient) u₀ a)).hom.app (omega P
        h) ≫
      (pull P u₀).map (((sourceEtale P a h).symm ≪≫
        (FiniteEtaleNormalization.congr P (a ≫ h) (h₀ ≫ b) (sqh).w).app
          (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (comp P h₀ b).app (coefficientUnit (ModuleCat.{u + 1} P.Coefficient) _) ≪≫
        (exceptional P h₀).mapIso (eta P b))).hom ≫
      beta P h₀ h₁₀ v₀ u₀ sq₀)  := by
  exact ⟨sigma_open_restriction P, sourceEtale_open_restriction P,
    beta_open_restriction P⟩

end AlgebraicGeometry.ProEtale.DualizingLocality
