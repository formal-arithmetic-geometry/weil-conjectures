/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectTransportProfile
public import WeilConjectures.CategoryTheory.Adjunction.TowerTransitionTransport
import all WeilConjectures.Algebra.Homology.SuccessiveDerivedQuotientNormalization

/-! # Intrinsic completeness along isomorphisms of coefficient data

The finite reduction towers of a completed object and of its transport along the completed
isomorphism of a datum isomorphism are identified, compatibly with the transitions. A
derived-limit presentation therefore transports, and with the Roos triangle of the
completion reflector it gives intrinsic completeness.

Source: Stacks Tags 099M and 099N (auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096

universe u
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_hasSheafify
attribute [-instance] WeilConjectures.integralCoefficientAbSheafify
attribute [-instance] WeilConjectures.integralCoefficientAbLocallyBijective

private local instance (priority := 100000) fixedSmall'' (T : AlgebraicGeometry.Scheme.{u}) :
    CategoryTheory.EssentiallySmall.{u + 1} T.ProEt :=
  CategoryTheory.essentiallySmallSelf.{0} _

private noncomputable local instance (priority := 100000) fixedSheafify''
    (T : AlgebraicGeometry.Scheme.{u}) :
    CategoryTheory.HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, 0} T

private local instance (priority := 100000) fixedLocallyBijective''
    (T : AlgebraicGeometry.Scheme.{u}) :
    (AlgebraicGeometry.Scheme.ProEt.topology T).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, 0} T

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

private theorem restrictComp_apply'
    {T : Scheme.{u}} {R S B : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : R ⟶ B) (h : a ≫ b = c)
    (M : pbcModules T B) (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcRestrictComp a b c h).hom.app M).val.app U x = x :=
  (pbcRestrictComp_exists a b c h).exists.choose_spec M U x

/-- Associativity of derived restriction comparisons, componentwise.
(auxiliary; not a blueprint node). -/
theorem pbcDerivedRestrictComp_assoc_app
    {T : Scheme.{u}} {R S B V : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ B) (c : B ⟶ V)
    (ab : R ⟶ B) (bc : S ⟶ V) (abc : R ⟶ V)
    (hab : a ≫ b = ab) (hbc : b ≫ c = bc)
    (habc : ab ≫ c = abc) (habc' : a ≫ bc = abc) (Y : DerivedCategory (pbcModules T V)) :
    (pbcDerivedRestrictComp a b ab hab).hom.app ((pbcDerivedRestrict c).obj Y) ≫
        (pbcDerivedRestrictComp ab c abc habc).hom.app Y =
      (pbcDerivedRestrict a).map ((pbcDerivedRestrictComp b c bc hbc).hom.app Y) ≫
        (pbcDerivedRestrictComp a bc abc habc').hom.app Y := by
  have h : Functor.isoWhiskerLeft (pbcDerivedRestrict c) (pbcDerivedRestrictComp a b ab hab) ≪≫
        pbcDerivedRestrictComp ab c abc habc =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (pbcDerivedRestrictComp b c bc hbc) (pbcDerivedRestrict a) ≪≫
        pbcDerivedRestrictComp a bc abc habc' := by
    apply SheafOfModules.SuccessiveDerivedQuotient.exactComp_assoc
    apply Iso.ext
    ext M U x
    simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Category.id_comp]
    change ((pbcRestrictComp ab c abc habc).hom.app M).val.app U
        (((pbcRestrictComp a b ab hab).hom.app ((pbcRestrict c).obj M)).val.app U x) =
      ((pbcRestrictComp a bc abc habc').hom.app M).val.app U
        (((pbcRestrictComp b c bc hbc).hom.app M).val.app U x)
    simp only [restrictComp_apply']
  have hY := congrArg (fun e ↦ e.hom.app Y) h
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Iso.symm_hom, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.id_comp] using hY

/-- Mates of isomorphisms between equivalences are isomorphisms.
(auxiliary; not a blueprint node). -/
theorem isIso_mateEquiv_symm_of_equivalences
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {G : C ⥤ C'} {H : D ⥤ D'}
    (a : L ⊣ R) (b : L' ⊣ R') [G.IsEquivalence] [H.IsEquivalence]
    (β : TwoSquare R H G R') [IsIso β.natTrans] :
    IsIso ((mateEquiv a b).symm β).natTrans := by
  let eG := G.asEquivalence.toAdjunction
  let eH := H.asEquivalence.toAdjunction
  let α := (mateEquiv a b).symm β
  have hi : IsIso (mateEquiv eH eG β).natTrans := by
    dsimp only [mateEquiv, Equiv.coe_fn_mk]
    infer_instance
  have he := iterated_mateEquiv_conjugateEquiv a b eG eH α
  change (mateEquiv eH eG ((mateEquiv a b) ((mateEquiv a b).symm β))).natTrans = _ at he
  rw [Equiv.apply_symm_apply] at he
  have : IsIso (conjugateEquiv (a.comp eH) (eG.comp b) α.natTrans) := he ▸ hi
  exact conjugateEquiv_of_iso (a.comp eH) (eG.comp b) α.natTrans

section Tower

variable {A A' : Type (u + 1)} [CommRing A] [CommRing A']
  (d : AdicCoefficientDatum A) (d' : AdicCoefficientDatum A')
  (φ : A ≃+* A') (hφ : d.ideal.map φ = d'.ideal) (T : Scheme.{u})

/-- Restriction of completed coefficients along the completed isomorphism.
(auxiliary; not a blueprint node). -/
abbrev AdicCoefficientDatum.transportBack :
    PbcCompletedDerived T d' ⥤ PbcCompletedDerived T d :=
  pbcDerivedRestrict (d.completionIso d' φ hφ T).hom

instance (n : ℕ) : (pbcDerivedRestrict (d.levelIso d' φ hφ T n).hom).IsEquivalence :=
  (pbcDerivedRestrictEquivalence (d.levelIso d' φ hφ T n)).isEquivalence_functor

instance : (d.transportBack d' φ hφ T).IsEquivalence :=
  (pbcDerivedRestrictEquivalence (d.completionIso d' φ hφ T)).isEquivalence_functor

theorem AdicCoefficientDatum.levelIso_quotient (n : ℕ) :
    (d.levelIso d' φ hφ T (n + 1)).hom ≫ pbcAdicQuotient T d' (n + 1) n (Nat.le_succ n) =
      pbcAdicQuotient T d (n + 1) n (Nat.le_succ n) ≫ (d.levelIso d' φ hφ T n).hom :=
  ((d.ringSystemHom d' φ hφ T).naturality (homOfLE (Nat.le_succ n)).op).symm

/-- The base change comparison of restrictions to a level. -/
def AdicCoefficientDatum.levelRestrictIso (n : ℕ) :
    pbcDerivedRestrict (pbcAdicProjection T d' n) ⋙ d.transportBack d' φ hφ T ≅
      pbcDerivedRestrict (d.levelIso d' φ hφ T n).hom ⋙
        pbcDerivedRestrict (pbcAdicProjection T d n) :=
  pbcDerivedRestrictComp (d.completionIso d' φ hφ T).hom (pbcAdicProjection T d' n)
      (pbcAdicProjection T d n ≫ (d.levelIso d' φ hφ T n).hom)
      (d.completionIso_hom_projection d' φ hφ T n) ≪≫
    (pbcDerivedRestrictComp (pbcAdicProjection T d n) (d.levelIso d' φ hφ T n).hom _ rfl).symm

/-- The base change comparison of quotient restrictions. -/
def AdicCoefficientDatum.quotientRestrictIso (n : ℕ) :
    pbcDerivedRestrict (pbcAdicQuotient T d' (n + 1) n (Nat.le_succ n)) ⋙
        pbcDerivedRestrict (d.levelIso d' φ hφ T (n + 1)).hom ≅
      pbcDerivedRestrict (d.levelIso d' φ hφ T n).hom ⋙
        pbcDerivedRestrict (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) :=
  pbcDerivedRestrictComp (d.levelIso d' φ hφ T (n + 1)).hom
      (pbcAdicQuotient T d' (n + 1) n (Nat.le_succ n))
      (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n) ≫ (d.levelIso d' φ hφ T n).hom)
      (d.levelIso_quotient d' φ hφ T n) ≪≫
    (pbcDerivedRestrictComp (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n))
      (d.levelIso d' φ hφ T n).hom _ rfl).symm

/-- The base change map of finite reductions, the mate of the restriction comparison. -/
def AdicCoefficientDatum.levelExtendMap (n : ℕ) :
    d.transportBack d' φ hφ T ⋙ pbcDerivedExtend (pbcAdicProjection T d n) ⟶
      pbcDerivedExtend (pbcAdicProjection T d' n) ⋙
        pbcDerivedRestrict (d.levelIso d' φ hφ T n).hom :=
  ((mateEquiv (pbcDerivedScalarAdjunction (pbcAdicProjection T d' n))
    (pbcDerivedScalarAdjunction (pbcAdicProjection T d n))).symm
    (TwoSquare.mk _ _ _ _ (d.levelRestrictIso d' φ hφ T n).hom)).natTrans

instance (n : ℕ) : IsIso (d.levelExtendMap d' φ hφ T n) :=
  isIso_mateEquiv_symm_of_equivalences _ _ _

/-- The base change isomorphism of finite reductions. -/
def AdicCoefficientDatum.levelExtendIso (n : ℕ) :
    d.transportBack d' φ hφ T ⋙ pbcDerivedExtend (pbcAdicProjection T d n) ≅
      pbcDerivedExtend (pbcAdicProjection T d' n) ⋙
        pbcDerivedRestrict (d.levelIso d' φ hφ T n).hom :=
  asIso (d.levelExtendMap d' φ hφ T n)

theorem AdicCoefficientDatum.levelExtendIso_unit (n : ℕ) (K : PbcCompletedDerived T d') :
    (d.transportBack d' φ hφ T).map
        ((pbcDerivedScalarAdjunction (pbcAdicProjection T d' n)).unit.app K) ≫
      (d.levelRestrictIso d' φ hφ T n).hom.app
        ((pbcDerivedExtend (pbcAdicProjection T d' n)).obj K) =
    (pbcDerivedScalarAdjunction (pbcAdicProjection T d n)).unit.app
        ((d.transportBack d' φ hφ T).obj K) ≫
      (pbcDerivedRestrict (pbcAdicProjection T d n)).map
        ((d.levelExtendIso d' φ hφ T n).hom.app K) :=
  unit_mateEquiv_symm _ _ (TwoSquare.mk _ _ _ _ (d.levelRestrictIso d' φ hφ T n).hom) K

/-- The finite reduction towers are intertwined by the base change comparisons.
(auxiliary; not a blueprint node). -/
theorem AdicCoefficientDatum.tower_baseChange (n : ℕ) (K : PbcCompletedDerived T d') :
    (d.transportBack d' φ hφ T).map
        (Adjunction.towerTransition (pbcDerivedScalarAdjunction (pbcAdicProjection T d' n))
          (pbcDerivedScalarAdjunction (pbcAdicProjection T d' (n + 1)))
          (pbcDerivedRestrictComp (pbcAdicProjection T d' (n + 1))
            (pbcAdicQuotient T d' (n + 1) n (Nat.le_succ n)) (pbcAdicProjection T d' n)
            (pbcAdicProjection_comp T d' (n + 1) n (Nat.le_succ n))) K) ≫
      (Adjunction.towerBaseChange (d.transportBack d' φ hφ T)
        (pbcDerivedRestrict (d.levelIso d' φ hφ T n).hom)
        (d.levelRestrictIso d' φ hφ T n) (d.levelExtendIso d' φ hφ T n) K).hom =
    (Adjunction.towerBaseChange (d.transportBack d' φ hφ T)
        (pbcDerivedRestrict (d.levelIso d' φ hφ T (n + 1)).hom)
        (d.levelRestrictIso d' φ hφ T (n + 1)) (d.levelExtendIso d' φ hφ T (n + 1)) K).hom ≫
      Adjunction.towerTransition (pbcDerivedScalarAdjunction (pbcAdicProjection T d n))
          (pbcDerivedScalarAdjunction (pbcAdicProjection T d (n + 1)))
          (pbcDerivedRestrictComp (pbcAdicProjection T d (n + 1))
            (pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)) (pbcAdicProjection T d n)
            (pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n)))
          ((d.transportBack d' φ hφ T).obj K) := by
  refine Adjunction.towerTransition_baseChange _ _ _ _ _ _ _ _ _ _ _
    (d.quotientRestrictIso d' φ hφ T n) _ _
    (d.levelExtendIso_unit d' φ hφ T n) (d.levelExtendIso_unit d' φ hφ T (n + 1)) ?_ K
  intro Y
  let ρh := (d.completionIso d' φ hφ T).hom
  let a1 := pbcAdicProjection T d' (n + 1)
  let q' := pbcAdicQuotient T d' (n + 1) n (Nat.le_succ n)
  let p' := pbcAdicProjection T d' n
  let P1 := pbcAdicProjection T d (n + 1)
  let q := pbcAdicQuotient T d (n + 1) n (Nat.le_succ n)
  let Pn := pbcAdicProjection T d n
  let l1 := (d.levelIso d' φ hφ T (n + 1)).hom
  let lh := (d.levelIso d' φ hφ T n).hom
  have h1 : ρh ≫ a1 = P1 ≫ l1 := d.completionIso_hom_projection d' φ hφ T (n + 1)
  have h2 : a1 ≫ q' = p' := pbcAdicProjection_comp T d' (n + 1) n (Nat.le_succ n)
  have h4 : ρh ≫ p' = Pn ≫ lh := d.completionIso_hom_projection d' φ hφ T n
  have hq : P1 ≫ q = Pn := pbcAdicProjection_comp T d (n + 1) n (Nat.le_succ n)
  have hl : l1 ≫ q' = q ≫ lh := d.levelIso_quotient d' φ hφ T n
  have h3 : (P1 ≫ l1) ≫ q' = Pn ≫ lh := by rw [Category.assoc, hl, ← Category.assoc, hq]
  have h5 : P1 ≫ (q ≫ lh) = Pn ≫ lh := by rw [← Category.assoc, hq]
  have A1 := pbcDerivedRestrictComp_assoc_app ρh a1 q' (P1 ≫ l1) p' (Pn ≫ lh) h1 h2 h3 h4 Y
  have A2 := pbcDerivedRestrictComp_assoc_app P1 l1 q' (P1 ≫ l1) (q ≫ lh) (Pn ≫ lh) rfl hl h3 h5 Y
  have A3 := pbcDerivedRestrictComp_assoc_app P1 q lh Pn (q ≫ lh) (Pn ≫ lh) hq rfl rfl h5 Y
  have A2' : (pbcDerivedRestrictComp (P1 ≫ l1) q' (Pn ≫ lh) h3).hom.app Y =
      (pbcDerivedRestrictComp P1 l1 (P1 ≫ l1) rfl).inv.app ((pbcDerivedRestrict q').obj Y) ≫
        (pbcDerivedRestrict P1).map ((pbcDerivedRestrictComp l1 q' (q ≫ lh) hl).hom.app Y) ≫
        (pbcDerivedRestrictComp P1 (q ≫ lh) (Pn ≫ lh) h5).hom.app Y := by
    rw [← A2, Iso.inv_hom_id_app_assoc]
  have A3' : (pbcDerivedRestrictComp P1 (q ≫ lh) (Pn ≫ lh) h5).hom.app Y =
      (pbcDerivedRestrict P1).map ((pbcDerivedRestrictComp q lh (q ≫ lh) rfl).inv.app Y) ≫
        (pbcDerivedRestrictComp P1 q Pn hq).hom.app ((pbcDerivedRestrict lh).obj Y) ≫
        (pbcDerivedRestrictComp Pn lh (Pn ≫ lh) rfl).hom.app Y := by
    rw [A3, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp]
  simp only [levelRestrictIso, quotientRestrictIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp, Category.assoc]
  rw [← reassoc_of% A1, A2', A3']
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_app, Category.comp_id]

end Tower

end AlgebraicGeometry.Scheme
