/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedOpenExchangeTransport
public import WeilConjectures.AlgebraicGeometry.CompletedOrdinaryComparisons
import WeilConjectures.AlgebraicGeometry.ProEtaleCanonicalAdjunctionUnit

/-! # Identity normalization before deriving open exchange

Source: Stacks Project, etale-cohomology.tex, lemma-shriek-base-change,
and sites-modules.tex, lemma-localize-morphism-ringed-sites.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

private theorem mateIdentity
    {C D : Type*} [Category C] [Category D]
    {J : C ⥤ D} {R : D ⥤ C} {F P : C ⥤ C} {G Q : D ⥤ D}
    (a : J ⊣ R) (b : F ⊣ P) (c : G ⊣ Q)
    (e : P ≅ 𝟭 C) (f : Q ≅ 𝟭 D)
    (γ : Q ⋙ R ⟶ R ⋙ P)
    (hγ : ∀ N, γ.app N ≫ e.hom.app (R.obj N) = R.map (f.hom.app N))
    (M : C) :
    ((conjugateEquiv (a.comp c) (b.comp a)).symm γ).app M ≫
        (c.leftAdjointIdIso f).hom.app (J.obj M) =
      J.map ((b.leftAdjointIdIso e).hom.app M) := by
  let α := (conjugateEquiv (a.comp c) (b.comp a)).symm γ
  have h₀ : conjugateEquiv a (b.comp a)
      (Functor.whiskerRight (b.leftAdjointIdIso e).hom J ≫
        (Functor.leftUnitor J).hom) =
      (Functor.rightUnitor R).inv ≫ Functor.whiskerLeft R e.inv := by
    rw [← conjugateEquiv_comp a (Adjunction.id.comp a),
      conjugateEquiv_leftUnitor_hom, conjugateEquiv_whiskerRight,
      Adjunction.conjugateEquiv_leftAdjointIdIso_hom]
  have h₁ : conjugateEquiv a (a.comp c)
      (Functor.whiskerLeft J (c.leftAdjointIdIso f).hom ≫
        (Functor.rightUnitor J).hom) =
      (Functor.leftUnitor R).inv ≫ Functor.whiskerRight f.inv R := by
    rw [← conjugateEquiv_comp a (a.comp Adjunction.id),
      conjugateEquiv_rightUnitor_hom, conjugateEquiv_whiskerLeft,
      Adjunction.conjugateEquiv_leftAdjointIdIso_hom]
  have hh : α ≫ Functor.whiskerLeft J (c.leftAdjointIdIso f).hom ≫
      (Functor.rightUnitor J).hom =
      Functor.whiskerRight (b.leftAdjointIdIso e).hom J ≫
        (Functor.leftUnitor J).hom := by
    apply (conjugateEquiv a (b.comp a)).injective
    rw [← conjugateEquiv_comp a (a.comp c), h₀, h₁]
    simp only [α, Equiv.apply_symm_apply]
    ext N
    simp only [NatTrans.comp_app, Functor.leftUnitor_inv_app,
      Functor.rightUnitor_inv_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.id_comp]
    apply (cancel_mono (e.hom.app (R.obj N))).1
    rw [Category.assoc, hγ, ← R.map_comp, Iso.inv_hom_id_app, R.map_id,
      Iso.inv_hom_id_app]
    rfl
  have h := NatTrans.congr_app hh M
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_hom_app] at h
  simpa [α] using h

private theorem leftIdentity_transport
    {C : Type*} [Category C] {F F' R R' : C ⥤ C}
    (a : F' ⊣ R') (h : F = F') (β : R ≅ R') (e : R' ≅ 𝟭 C) :
    ((a.ofNatIsoLeft (eqToIso h).symm).ofNatIsoRight β.symm).leftAdjointIdIso
        (β ≪≫ e) = eqToIso h ≪≫ a.leftAdjointIdIso e := by
  cases h
  apply Iso.ext
  ext M
  simp [Adjunction.leftAdjointIdIso_hom_app, ← Functor.map_comp_assoc]

namespace AlgebraicGeometry.Scheme

private theorem coefficientDirect_eq
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X Y : Scheme.{t}} (g : X ⟶ Y) :
    cbcCompletedCoefficientDirectMap d g = proEtaleRingDirectImageMap g
      (d.completedRing Y) (d.completedRing X) (d.integralRingIso g) := by
  unfold cbcCompletedCoefficientDirectMap proEtaleRingDirectImageMap
  rw [cbcDatumCoefficient_eq, Adjunction.homEquiv_unit]

private def moduleDirectIso
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X Y : Scheme.{t}} (g : X ⟶ Y) :
    cbcCompletedModuleDirectImage d g ≅ proEtaleRingModuleDirectImage g
      (d.completedRing Y) (d.completedRing X) (d.integralRingIso g) :=
  SheafOfModules.pushforwardCongr
    (congrArg (fun φ ↦ (sheafCompose (ProEt.topology Y)
      (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map φ)
        (coefficientDirect_eq d g))

private theorem moduleDirectIso_hom_sections
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X Y : Scheme.{t}} (g : X ⟶ Y)
    (N : pbcModules X (pbcAdicCompletion X d)) (V : Y.ProEtᵒᵖ)
    (x : ((cbcCompletedModuleDirectImage d g).obj N).val.obj V) :
    ((moduleDirectIso d g).hom.app N).val.app V x = x := rfl

private theorem moduleDirectIso_inv_sections
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X Y : Scheme.{t}} (g : X ⟶ Y)
    (N : pbcModules X (pbcAdicCompletion X d)) (V : Y.ProEtᵒᵖ)
    (x : ((proEtaleRingModuleDirectImage g (d.completedRing Y) (d.completedRing X)
      (d.integralRingIso g)).obj N).val.obj V) :
    ((moduleDirectIso d g).inv.app N).val.app V x = x := rfl

private theorem tensor_transport (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ : R ⟶ S)
    (M : pbcModules T R) (V : T.ProEtᵒᵖ) (s : S.obj.obj V) (x : M.val.obj V)
    (h : (pbcExtend φ).obj M = SheafOfModules.changeOfRings.{t, t + 1, t + 1} φ M) :
    (eqToHom h).val.app V (pbcTensorSection φ M V s x) =
      (toSheafify (ProEt.topology T)
        (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1}
          (J := ProEt.topology T) φ M).presheaf).app V
              (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x) := by
  let h₀ := (completedAdicChangeData T φ).choose_spec.choose M
  have hh : (eqToHom h₀.symm ≫ eqToHom h) = 𝟙 _ := by simp
  exact congrArg (fun f ↦ f.val.app V
    ((toSheafify (ProEt.topology T)
      (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1}
        (J := ProEt.topology T) φ M).presheaf).app V
            (s ⊗ₜ[R.obj.obj V, (φ.hom.app V).hom] x))) hh

private theorem tensor_transport_coeff (T : Scheme.{t})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{t + 1}} (φ ψ : R ⟶ S)
    (hφ : φ = ψ) (M : pbcModules T R) (V : T.ProEtᵒᵖ)
    (s : S.obj.obj V) (x : M.val.obj V)
    (h : (pbcExtend φ).obj M = SheafOfModules.changeOfRings.{t, t + 1, t + 1} ψ M) :
    (eqToHom h).val.app V (pbcTensorSection φ M V s x) =
      (toSheafify (ProEt.topology T)
        (SheafOfModules.changeOfRingsPresheaf.{t, t + 1, t + 1}
          (J := ProEt.topology T) ψ M).presheaf).app V
              (s ⊗ₜ[R.obj.obj V, (ψ.hom.app V).hom] x) := by
  subst ψ
  exact tensor_transport T φ M V s x h

private theorem pullUnit_transport_sections
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X Y : Scheme.{t}} (g : X ⟶ Y)
    (M : pbcModules Y (pbcAdicCompletion Y d)) (V : Y.ProEt)
    (x : M.val.obj (op V)) :
    (((eqToIso (cbcDatumModulePull_eq d g)).hom.app M).val.app
      (op ((proEtaleBaseChange g).obj V)))
        (pbcTensorSection (completedCoefficientMap g d)
          ((proEtaleModuleInverseImage g (pbcAdicCompletion Y d)).obj M)
          (op ((proEtaleBaseChange g).obj V)) 1
          (((cbcModelPullbackAdjunction d g).unit.app
            ((proEtaleModuleToModel
              (reductionModuleRing Y (pbcAdicCompletion Y d))).obj M)).val.app
                (op (AsSmall.up.obj V)) x)) =
      ((proEtaleRingModuleAdjunction g (d.completedRing Y) (d.completedRing X)
        (d.integralRingIso g)).unit.app M).val.app (op V) x := by
  rw [proEtaleRingModuleAdjunction_normalized g (d.completedRing Y)
    (d.completedRing X) (d.integralRingIso g) M V x]
  unfold proEtaleRingModuleUnitSection
  rw [eqToIso.hom, eqToHom_app]
  exact (tensor_transport_coeff X _ _ (cbcDatumCoefficient_eq d g)
    ((proEtaleModuleInverseImage g (pbcAdicCompletion Y d)).obj M)
    (op ((proEtaleBaseChange g).obj V)) 1
    (((cbcModelPullbackAdjunction d g).unit.app
      ((proEtaleModuleToModel
        (reductionModuleRing Y (pbcAdicCompletion Y d))).obj M)).val.app
          (op (AsSmall.up.obj V)) x)
    (congrArg (fun F ↦ F.obj M) (cbcDatumModulePull_eq d g)))
    |>.trans (by rfl)

private def transportedAdjunction
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X Y : Scheme.{t}} (g : X ⟶ Y) :
    completedModulePullback g d ⊣ cbcCompletedModuleDirectImage d g :=
  ((proEtaleRingModuleAdjunction g (d.completedRing Y) (d.completedRing X)
    (d.integralRingIso g)).ofNatIsoLeft (eqToIso (cbcDatumModulePull_eq d g)).symm
      ).ofNatIsoRight (moduleDirectIso d g).symm

private theorem transportedAdjunction_eq
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {X Y : Scheme.{t}} (g : X ⟶ Y) :
    transportedAdjunction d g = cbcModulePullbackAdjunction d g := by
  apply (cbcModulePullbackAdjunction_exists d g).unique
  · intro M V x
    simp only [transportedAdjunction, Adjunction.ofNatIsoLeft_unit,
      Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Iso.symm_hom]
    change (((eqToIso (cbcDatumModulePull_eq d g)).inv.app M).val.app
      (op ((proEtaleBaseChange g).obj V)))
        (((proEtaleRingModuleAdjunction g (d.completedRing Y) (d.completedRing X)
          (d.integralRingIso g)).unit.app M).val.app (op V) x) = _
    rw [← pullUnit_transport_sections d g M V x]
    have hh := (eqToIso (cbcDatumModulePull_eq d g)).hom_inv_id_app M
    exact congrArg (fun f ↦ f.val.app (op ((proEtaleBaseChange g).obj V))
      (pbcTensorSection (completedCoefficientMap g d)
        ((proEtaleModuleInverseImage g (pbcAdicCompletion Y d)).obj M)
        (op ((proEtaleBaseChange g).obj V)) 1
        (((cbcModelPullbackAdjunction d g).unit.app
          ((proEtaleModuleToModel
            (reductionModuleRing Y (pbcAdicCompletion Y d))).obj M)).val.app
              (op (AsSmall.up.obj V)) x))) hh
  · exact (cbcModulePullbackAdjunction_exists d g).exists.choose_spec

private def completedPushId
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) (T : Scheme.{t}) :
    cbcCompletedModuleDirectImage d (𝟙 T) ≅ 𝟭 _ :=
  moduleDirectIso d (𝟙 T) ≪≫ d.modulePushId T

private theorem completedPushId_sections
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) (T : Scheme.{t})
    (N : pbcModules T (pbcAdicCompletion T d)) (V : T.ProEt)
    (x : ((cbcCompletedModuleDirectImage d (𝟙 T)).obj N).val.obj (op V)) :
    ((completedPushId d T).hom.app N).val.app (op V) x =
      N.val.map ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).inv.app V).op x := by
  change ((d.modulePushId T).hom.app N).val.app (op V)
    (((moduleDirectIso d (𝟙 T)).hom.app N).val.app (op V) x) = _
  rw [moduleDirectIso_hom_sections]
  exact (d.modulePushId_existsUnique T).choose_spec.1 N V x

private theorem rightExchange_identity
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    (sq : OpenImmersionSquare (𝟙 U) j j (𝟙 T))
    (N : pbcModules T (pbcAdicCompletion T d)) :
    (cbcRightExchange d sq).app N ≫
        (completedPushId d U).hom.app ((cbcOpenRestriction d j inferInstance).obj N) =
      (cbcOpenRestriction d j inferInstance).map ((completedPushId d T).hom.app N) := by
  ext V x
  change ((completedPushId d U).hom.app
      ((cbcOpenRestriction d j inferInstance).obj N)).val.app V
        (((cbcRightExchange d sq).app N).val.app V x) =
    ((completedPushId d T).hom.app N).val.app
      (op ((cbcOpenSiteFunctor j inferInstance).obj V.unop)) x
  rw [completedPushId_sections, completedPushId_sections]
  have hex := (cbcRightExchange_exists d sq).exists.choose_spec N V x
  change (((cbcRightExchange d sq).app N).val.app V) x = _ at hex
  change N.val.map
      (((cbcOpenSiteFunctor j inferInstance).map
        ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ U).inv.app V.unop)).op)
      (((cbcRightExchange d sq).app N).val.app V x) = _
  rw [hex]
  let a := (MorphismProperty.Over.pullbackMapComparison
    (cbcOpenWeaklyEtale j sq.isOpenImmersion)
    (cbcOpenWeaklyEtale j sq.isOpenImmersion') sq.toCommSq).app V.unop
  let b := (cbcOpenSiteFunctor j inferInstance).map
    ((MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ U).inv.app V.unop)
  let c := (MorphismProperty.Over.pullbackId @WeaklyEtale ⊤ T).inv.app
    ((cbcOpenSiteFunctor j inferInstance).obj V.unop)
  have hab : b ≫ a = c := by
    apply MorphismProperty.Over.Hom.ext
    change b.left ≫ a.left = c.left
    apply pullback.hom_ext
    · change (b.left ≫ a.left) ≫ pullback.fst (V.unop.hom ≫ j) (𝟙 T) =
        c.left ≫ pullback.fst (V.unop.hom ≫ j) (𝟙 T)
      dsimp only [a, b, c, cbcOpenSiteFunctor]
      simp only [MorphismProperty.Over.map_map_left,
        MorphismProperty.Over.pullbackMapComparison_app_left,
        MorphismProperty.Over.pullbackId_inv_app_left_fst,
        MorphismProperty.Over.map_obj_hom, Category.assoc,
        pullback.lift_fst]
      erw [MorphismProperty.Over.pullbackId_inv_app_left_fst]
      rfl
    · change (b.left ≫ a.left) ≫ pullback.snd (V.unop.hom ≫ j) (𝟙 T) =
        c.left ≫ pullback.snd (V.unop.hom ≫ j) (𝟙 T)
      dsimp only [a, b, c, cbcOpenSiteFunctor]
      simp only [MorphismProperty.Over.map_map_left,
        MorphismProperty.Over.pullbackMapComparison_app_left,
        MorphismProperty.Over.pullbackId_inv_app_left_fst,
        MorphismProperty.Over.map_obj_hom, Category.assoc,
        pullback.lift_snd_assoc, pullback.lift_snd, Category.id_comp]
      erw [MorphismProperty.Over.pullbackId_inv_app_left,
        MorphismProperty.Over.pullbackId_inv_app_left,
        pullback.lift_snd_assoc, pullback.lift_snd]
      rfl
  change N.val.map b.op (N.val.map a.op x) = N.val.map c.op x
  have hmap : a.op ≫ b.op = c.op := by
    rw [← CategoryTheory.op_comp, hab]
  exact (N.val.map_comp_apply a.op b.op x).symm.trans
    (N.val.congr_map_apply hmap x)

/-- Identity on the ordinary module pullback, with the section-normalized adjunction.
Source: Stacks 03D8 and 03DI
(blueprint: lem-cbc-underived-open-exchange-identity). -/
def cbcModulePullId {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    (T : Scheme.{t}) : completedModulePullback (𝟙 T) d ≅ 𝟭 _ :=
  eqToIso (cbcDatumModulePull_eq d (𝟙 T)) ≪≫
    (proEtaleRingModuleAdjunction (𝟙 T) (d.completedRing T) (d.completedRing T)
      (d.integralRingIso (𝟙 T))).leftAdjointIdIso (d.modulePushId T)

private theorem modulePullId_eq
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A) (T : Scheme.{t}) :
    (cbcModulePullbackAdjunction d (𝟙 T)).leftAdjointIdIso (completedPushId d T) =
      cbcModulePullId d T := by
  rw [← transportedAdjunction_eq]
  exact leftIdentity_transport _ _ _ _

/-- The underived inverse open exchange respects the normalized module identity.
Source: Stacks, etale-cohomology.tex, lemma-shriek-base-change, and
sites-modules.tex, lemma-localize-morphism-ringed-sites; identity specialization
(blueprint: lem-cbc-underived-open-exchange-identity).
Proof: identify the completed scalar maps with the datum maps by their finite
projections. Their normalized pullback adjunctions agree: on the model site both
units send a section x to 1 tensor x, and tensor generators and sheafification
force equality of the Hom equivalences. On a pro-etale object V of U, the right
exchange restricts along the canonical map V times_U U to V times_T T. Compose
with the two direct-image identity comparisons, which restrict along the inverse
pullback identities. The composites agree because both underlying scheme maps
have first projection the identity and second projection the structure map.
Functoriality of restriction proves the right-adjoint square on every section,
including over an empty open. Transpose through the two composite adjunctions.
The triangle identities cancel their units and counits and give the displayed
left-adjoint square. The isomorphism on each identity pullback is precisely
cbcModulePullId, since it is obtained from the same section-normalized direct
image by leftAdjointIdIso. This proof uses neither completeness nor a bound. -/
theorem cbcUnderivedInverseExchange_identity
    {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
    {U T : Scheme.{t}} (j : U ⟶ T) [IsOpenImmersion j]
    (sq : OpenImmersionSquare (𝟙 U) j j (𝟙 T))
    (M : pbcModules U (pbcAdicCompletion U d)) :
    (cbcUnderivedInverseExchange d sq).app M ≫
        (cbcModulePullId d T).hom.app ((cbcOpenShriek d j inferInstance).obj M) =
      (cbcOpenShriek d j inferInstance).map ((cbcModulePullId d U).hom.app M) := by
  simpa only [modulePullId_eq, cbcUnderivedInverseExchange] using
    mateIdentity (cbcOpenAdjunction d j inferInstance)
      (cbcModulePullbackAdjunction d (𝟙 U)) (cbcModulePullbackAdjunction d (𝟙 T))
      (completedPushId d U) (completedPushId d T) (cbcRightExchange d sq)
      (rightExchange_identity d j sq) M

end AlgebraicGeometry.Scheme
