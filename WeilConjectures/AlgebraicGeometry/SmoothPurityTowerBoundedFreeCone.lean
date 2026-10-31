/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityTowerReconstructionData
public import WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower
import WeilConjectures.Algebra.Homology.LinearScalarConeExactProducts
import WeilConjectures.Algebra.Homology.RegularQuotientConeAdjoint
import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Exists
import Mathlib.CategoryTheory.Adjunction.Unique
import all WeilConjectures.AlgebraicGeometry.EllCoefficientFiber

/-! Strict ell-adic models and their bounded-free cone comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace AlgebraicGeometry.ProEtale
attribute [-instance] spCoefficientModulesAbelian
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] WeilConjectures.completedIntegralCoefficientSheafUnrestricted
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})
  (D : SpCoefficientTowersAbelian l E T)

local instance : HasSheafify (Scheme.ProEt.topology T) CommRingCat.{u + 1} :=
  WeilConjectures.integralCoefficientRingSheafify.{u, u} T

local instance : HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbSheafify.{u, u} T

local instance : (Scheme.ProEt.topology T).WEqualsLocallyBijective
    AddCommGrpCat.{u + 1} :=
  WeilConjectures.integralCoefficientAbLocallyBijective.{u, u} T

private def ellPowerSection (n : ℕ) :
    (unit (WeilConjectures.completedIntegralCoefficientSheafUnrestricted.{u, u} l E T)).sections :=
  spCompletedScalar l E T ((l : Padic.coefficientExtensionIntegers l E) ^ (n + 1))

private theorem ellPowerScalar (n : ℕ)
    (P : CochainComplex (WeilConjectures.scalarReductionSource.{u, u} l E T) ℤ) :
    (RegularQuotientCone.complexScalar
      (WeilConjectures.completedIntegralCommRingSheafUnrestricted.{u, u} l E T)
      (ellPowerSection l E T n)).app P = (l : ℤ) ^ (n + 1) • 𝟙 P := by
  apply HomologicalComplex.hom_ext
  intro q
  ext V x
  change ((WeilConjectures.integralConstantToCompletionOfUniverses.{u, u} l E T).hom.app V
    ((toSheafify (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj
        (CommRingCat.of.{u+1} (ULift.{u+1} (Padic.coefficientExtensionIntegers l E))))).app V
          (ULift.up ((l : Padic.coefficientExtensionIntegers l E) ^ (n + 1))))) • x = _
  simp only [show ULift.up ((l : Padic.coefficientExtensionIntegers l E) ^ (n + 1)) =
    ((l : ULift.{u+1} (Padic.coefficientExtensionIntegers l E)) ^ (n + 1)) from rfl,
    map_pow, map_natCast]
  let ev := HomologicalComplex.eval
    (WeilConjectures.scalarReductionSource.{u, u} l E T) (.up ℤ) q ⋙
    SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ V
  have hev := congrArg (fun f ↦ f.hom x)
    (ev.map_zsmul (f := 𝟙 P) (r := (l : ℤ) ^ (n + 1)))
  rw [ev.map_id, ModuleCat.hom_zsmul, LinearMap.smul_apply,
    ModuleCat.hom_id, LinearMap.id_apply] at hev
  have hs : (l : (WeilConjectures.completedIntegralCommRingSheafUnrestricted.{u, u}
      l E T).obj.obj V) ^ (n + 1) • x = ((l : ℤ) ^ (n + 1)) • x := by
    rw [← Int.cast_smul_eq_zsmul
      ((WeilConjectures.completedIntegralCommRingSheafUnrestricted.{u, u} l E T).obj.obj V),
      Int.cast_pow, Int.cast_natCast]
  exact hs.trans hev.symm

private def restrictionUnitIso {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{u}}
    {f g : R ⟶ S} (h : f = g) :
    (restrictScalars f).obj (unit S) ≅ (restrictScalars g).obj (unit S) :=
  eqToIso (congrArg (fun q ↦ (restrictScalars q).obj (unit S)) h)

private theorem restrictionUnitIso_map {C : Type*} [Category C]
    {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{u}}
    {f g : R ⟶ S} (h : f = g) :
    spRingModuleMap f ≫ (restrictionUnitIso h).hom = spRingModuleMap g := by
  subst g
  simp [restrictionUnitIso]

private theorem ellPowerExact (n : ℕ) :
    ∃ ht : (RegularQuotientCone.scalar
      (WeilConjectures.completedIntegralCommRingSheafUnrestricted.{u, u} l E T)
      (ellPowerSection l E T n)).app
      (unit (WeilConjectures.completedIntegralCoefficientSheafUnrestricted.{u, u} l E T)) ≫
        RegularQuotientCone.ringMap (spCompletedEllCommProjection l E T n) = 0,
      (ShortComplex.mk _ _ ht).ShortExact := by
  obtain ⟨_, _, _, hm, hq, _⟩ := sp_completed_coefficients_regular l E T
  obtain ⟨e, he, _⟩ := hq n
  let R := WeilConjectures.completedIntegralCommRingSheafUnrestricted.{u, u} l E T
  let f := endoPow
    (globalSectionMultiplication R (spCompletedScalar l E T l)) (n + 1)
  have hf : (RegularQuotientCone.scalar R (ellPowerSection l E T n)).app
      (unit (WeilConjectures.completedIntegralCoefficientSheafUnrestricted.{u, u} l E T)) = f := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro V
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (WeilConjectures.completedIntegralCommRingSheafUnrestricted.{u, u}
      l E T).obj.obj V at x
    have hp := completedPower_apply l E T (l : Padic.coefficientExtensionIntegers l E)
      (n + 1) V x
    change ((spCompletedScalarSection l E T
      ((l : Padic.coefficientExtensionIntegers l E) ^ (n + 1))).val V) * x =
      (endoPow (globalSectionMultiplication
        (WeilConjectures.completedIntegralCommRingSheafUnrestricted.{u, u} l E T)
        (spCompletedScalar l E T l)) (n + 1)).val.app V x
    rw [hp]
    change ((spCompletedScalarSection l E T
      ((l : Padic.coefficientExtensionIntegers l E) ^ (n + 1))).val V) * x =
        x * ((spCompletedScalarSection l E T l).val V) ^ (n + 1)
    have hpow :
        (@id ((WeilConjectures.completedIntegralCommRingSheafUnrestricted.{u, u}
          l E T).obj.obj V)
          ((spCompletedScalarSection l E T
            ((l : Padic.coefficientExtensionIntegers l E) ^ (n + 1))).val V)) =
        (@id ((WeilConjectures.completedIntegralCommRingSheafUnrestricted.{u, u}
          l E T).obj.obj V) ((spCompletedScalarSection l E T l).val V)) ^ (n + 1) := by
      change (WeilConjectures.integralConstantToCompletionOfUniverses.{u, u} l E T).hom.app V
        ((toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of.{u+1}
            (ULift.{u+1} (Padic.coefficientExtensionIntegers l E))))).app V
              (ULift.up ((l : Padic.coefficientExtensionIntegers l E) ^ (n + 1)))) = _
      rw [show ULift.up ((l : Padic.coefficientExtensionIntegers l E) ^ (n + 1)) =
        (ULift.up (l : Padic.coefficientExtensionIntegers l E)) ^ (n + 1) from rfl,
        map_pow, map_pow]
      rfl
    exact (congrArg (fun z : (WeilConjectures.completedIntegralCommRingSheafUnrestricted.{u, u}
      l E T).obj.obj V ↦ z * x) hpow).trans (mul_comm _ _)
  have h : (sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u+1} RingCat.{u+1})).map
      (spCompletedEllCommProjection l E T n) = spCompletedEllProjection l E T n := by
    exact Functor.map_preimage _ _
  let b := restrictionUnitIso h.symm
  have hb : spRingModuleMap (spCompletedEllProjection l E T n) ≫ b.hom =
      RegularQuotientCone.ringMap (spCompletedEllCommProjection l E T n) := by
    exact restrictionUnitIso_map h.symm
  let e' := e ≪≫ b
  have he' : cokernel.π f ≫ e'.hom =
      RegularQuotientCone.ringMap (spCompletedEllCommProjection l E T n) := by
    dsimp only [e', Iso.trans_hom]
    rw [← Category.assoc, he, hb]
  have : Mono f := hm _ (Or.inl rfl) n
  have hs : (ShortComplex.mk f (cokernel.π f) (cokernel.condition f)).ShortExact :=
    { exact := ShortComplex.exact_cokernel f }
  have ht : (RegularQuotientCone.scalar R (ellPowerSection l E T n)).app
      (unit (WeilConjectures.completedIntegralCoefficientSheafUnrestricted.{u, u} l E T)) ≫
        RegularQuotientCone.ringMap (spCompletedEllCommProjection l E T n) = 0 := by
    rw [hf, ← he']
    simp
  refine ⟨ht, ?_⟩
  exact ShortComplex.shortExact_of_iso
    (S₁ := ShortComplex.mk f (cokernel.π f) (cokernel.condition f))
    (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e'
      (by simpa only [Iso.refl_hom, Category.id_comp, Category.comp_id] using hf)
      (by simpa only [Iso.refl_hom, Category.id_comp] using he'.symm)) hs

private theorem inverse_factor {C : Type*} [Category C]
    {X Y Z : C} (r : X ≅ Y) (f : Y ≅ Z) (v : X ≅ Z)
    (h : v.hom = r.hom ≫ f.hom) : f.hom ≫ v.inv = r.inv := by
  calc
    f.hom ≫ v.inv = r.inv ≫ (r.hom ≫ f.hom) ≫ v.inv := by simp
    _ = r.inv := by rw [← h]; simp

private theorem map_adjunct_comparison
    {C B : Type*} [Category C] [Category B]
    {L T : C ⥤ B} {R V : B ⥤ C}
    (adj : L ⊣ R) (badj : T ⊣ V) (v : V ≅ R)
    (X : C) (Y : B) (a : X ⟶ R.obj Y) :
    R.map ((adj.homEquiv X Y).symm a) =
      R.map ((adj.leftAdjointUniq (badj.ofNatIsoRight v)).hom.app X) ≫
        v.inv.app (T.obj X) ≫
        V.map ((badj.homEquiv X Y).symm (a ≫ v.inv.app Y)) ≫ v.hom.app Y := by
  let ba := badj.ofNatIsoRight v
  let k := adj.leftAdjointUniq ba
  have hk : (adj.homEquiv X Y).symm a =
      k.hom.app X ≫ (ba.homEquiv X Y).symm a := by
    apply (adj.homEquiv X Y).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Functor.map_comp,
      ← Category.assoc, Adjunction.unit_leftAdjointUniq_hom_app]
    exact ((ba.homEquiv X Y).apply_symm_apply a).symm
  rw [hk, Functor.map_comp]
  dsimp only [ba]
  rw [Adjunction.homEquiv_ofNatIsoRight_symm_apply]
  have hn (g : T.obj X ⟶ Y) :
      R.map g = v.inv.app _ ≫ V.map g ≫ v.hom.app _ := by
    rw [v.hom.naturality]
    simp
  rw [hn]

private theorem inv_hom_factor {C : Type*} [Category C]
    {X Y Z : C} (r : X ≅ Y) (f : Y ≅ Z) (v : X ≅ Z)
    (h : v.hom = r.hom ≫ f.hom) : r.inv ≫ v.hom = f.hom := by
  rw [h]
  simp

private theorem map_desc_eq {C : Type*} [Category C] [Abelian C]
    {P N : CochainComplex C ℤ} {s t : P ⟶ P} (h : s = t)
    (f : P ⟶ N) (hf : t ≫ f = 0) :
    CochainComplex.mappingCone.map s t (𝟙 P) (𝟙 P) (by simpa using h) ≫
        CochainComplex.mappingCone.desc t 0 f (by simp [hf]) =
      CochainComplex.mappingCone.desc s 0 f (by simp [h, hf]) := by
  subst t
  simp only [CochainComplex.mappingCone.map_id, Category.id_comp]

private theorem comparison_formula
    {C B : Type*} [Category C] [Category B]
    {L T : C ⥤ B} {R V : B ⥤ C} {D G : C ⥤ C}
    (adj : L ⊣ R) (badj : T ⊣ V) (v : V ≅ R)
    (bA : D ≅ T ⋙ V) (e : D ≅ G)
    (X : C) (Y : B) (a : X ⟶ R.obj Y) (q : X ⟶ V.obj Y)
    (g : D.obj X ⟶ V.obj Y) (z : G.obj X ⟶ R.obj Y)
    (hq : a ≫ v.inv.app Y = q)
    (hb : V.map ((badj.homEquiv X Y).symm q) = bA.inv.app X ≫ g)
    (hz : e.hom.app X ≫ z = g ≫ v.hom.app Y) :
    R.map ((adj.homEquiv X Y).symm a) =
      (Functor.isoWhiskerRight (adj.leftAdjointUniq (badj.ofNatIsoRight v)) R ≪≫
        (bA ≪≫ Functor.isoWhiskerLeft T v).symm ≪≫ e).hom.app X ≫ z := by
  rw [map_adjunct_comparison adj badj v, hq, hb]
  dsimp only [Iso.trans_hom, Iso.symm_hom, Iso.trans_inv,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, NatTrans.comp_app]
  simp only [Category.assoc]
  rw [hz]

private theorem composition_comparison {C : Type*} [Category C]
    {X Y Z W A B H : C} (e : X ⟶ Y) (c : Y ⟶ Z)
    (u : X ⟶ W) (v : W ⟶ Z) (z : Z ⟶ A) (z' : W ⟶ A)
    (r : A ⟶ B) (s : B ⟶ H) (t : A ⟶ H)
    (he : e ≫ c = u ≫ v) (hz : v ≫ z = z') (hr : r ≫ s = t) :
    e ≫ (c ≫ z ≫ t) = (u ≫ z' ≫ r) ≫ s := by
  calc
    e ≫ (c ≫ z ≫ t) = (e ≫ c) ≫ z ≫ t := by simp only [Category.assoc]
    _ = (u ≫ v) ≫ z ≫ t := by rw [he]
    _ = u ≫ (v ≫ z) ≫ t := by simp only [Category.assoc]
    _ = u ≫ z' ≫ t := by rw [hz]
    _ = (u ≫ z' ≫ r) ≫ s := by rw [Category.assoc, Category.assoc, hr]

private def ellConeIso (n : ℕ) :
    SheafOfModules.RegularQuotientCone.cone
      (WeilConjectures.completedIntegralCommRingSheafUnrestricted.{u, u} l E T)
      (ellPowerSection l E T n) ≅
        CochainComplex.LinearScalarCone.cochain
          (A := WeilConjectures.scalarReductionSource.{u, u} l E T)
          ((l : ℤ) ^ (n + 1)) := by
  let a : 𝟭 (CochainComplex (WeilConjectures.scalarReductionSource.{u, u} l E T) ℤ) ⟶
      𝟭 (CochainComplex (WeilConjectures.scalarReductionSource.{u, u} l E T) ℤ) :=
    SheafOfModules.RegularQuotientCone.complexScalar
    (WeilConjectures.completedIntegralCommRingSheafUnrestricted.{u, u} l E T)
    (ellPowerSection l E T n)
  let H : CochainComplex (WeilConjectures.scalarReductionSource.{u, u} l E T) ℤ ⥤
      Arrow (CochainComplex (WeilConjectures.scalarReductionSource.{u, u} l E T) ℤ) := {
    obj := fun P ↦ Arrow.mk (a.app P)
    map := fun f ↦ Arrow.homMk f f (by
      simpa only [Functor.id_map, Arrow.mk_hom] using a.naturality f) }
  let e : H ≅ CochainComplex.smulArrow
      (𝒜 := WeilConjectures.scalarReductionSource.{u, u} l E T)
      ((l : ℤ) ^ (n + 1)) :=
    NatIso.ofComponents (fun P ↦ Arrow.isoMk (Iso.refl _) (Iso.refl _)
      (by
        change (𝟙 P) ≫ ((l : ℤ) ^ (n + 1) • 𝟙 P) =
          a.app P ≫ (𝟙 P)
        exact (Category.id_comp _).trans
          ((ellPowerScalar l E T n P).symm.trans (Category.comp_id _).symm))) (by
        intro P Q f
        ext <;> simp [H])
  exact Functor.isoWhiskerRight e CochainComplex.ConeCoimage.cone

set_option maxHeartbeats 2000000 in
-- Localization whiskering compares large coefficient functor records.
private theorem strictCoefficientAdjoint (n : ℕ) :
    ∃ A : (D.scalar (spCompletedEllCommProjection l E T n)).model.T ⋙
        (spCompletedEllRestriction l E T n).mapDerivedCategory ≅
      CochainComplex.LinearScalarCone.derived
        (A := WeilConjectures.scalarReductionSource.{u, u} l E T)
        ((l : ℤ) ^ (n + 1)),
    ∀ (P : CochainComplex (WeilConjectures.scalarReductionSource.{u, u} l E T) ℤ)
      (N : CochainComplex (Scheme.proEtaleRingModules T
        (Scheme.proEtaleConstantRing T (Padic.coefficientExtensionIntegers l E ⧸
          spEllIdeal l E ^ (n + 1)))) ℤ)
      (f : P ⟶ ((spCompletedEllRestriction l E T n).mapHomologicalComplex
        (.up ℤ)).obj N)
      (hf : ((l : ℤ) ^ (n + 1) • 𝟙 P) ≫ f = 0),
      ((spCompletedEllRestriction l E T n).mapDerivedCategory).map
        (((D.scalar (spCompletedEllCommProjection l E T n)).adjunction.homEquiv
          (DerivedCategory.Q.obj P)
          ((@DerivedCategory.Q _ _ _ (HasDerivedCategory.standard _)).obj N)).symm
          (DerivedCategory.Q.map f ≫
            (spCompletedEllRestriction l E T n).mapDerivedCategoryFactors.inv.app N)) =
      A.hom.app (DerivedCategory.Q.obj P) ≫
        (CochainComplex.LinearScalarCone.comparison
          ((l : ℤ) ^ (n + 1))).hom.app P ≫
        DerivedCategory.Q.map (CochainComplex.mappingCone.desc
          ((l : ℤ) ^ (n + 1) • 𝟙 P) 0 f (by simp [hf])) ≫
        (spCompletedEllRestriction l E T n).mapDerivedCategoryFactors.inv.app N := by
  classical
  let adj := (D.scalar (spCompletedEllCommProjection l E T n)).adjunction
  let φ := spCompletedEllCommProjection l E T n
  let d := (D.scalar φ).model
  obtain ⟨ht, hexact⟩ := ellPowerExact l E T n
  obtain ⟨b⟩ := SheafOfModules.RegularQuotientCone.nonempty_augmentation
    (C := T.ProEt) (J := Scheme.ProEt.topology T)
    φ (ellPowerSection l E T n) ht hexact d
  let G := CochainComplex.LinearScalarCone.derived
    (A := WeilConjectures.scalarReductionSource.{u, u} l E T)
    ((l : ℤ) ^ (n + 1))
  let comp := CochainComplex.LinearScalarCone.comparison
    (A := WeilConjectures.scalarReductionSource.{u, u} l E T)
    ((l : ℤ) ^ (n + 1))
  let e : DerivedCategory.Q ⋙ b.D ≅ DerivedCategory.Q ⋙ G :=
    b.cone_factor ≪≫ Functor.isoWhiskerRight (ellConeIso l E T n) DerivedCategory.Q ≪≫
      comp.symm
  let FF := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (WeilConjectures.scalarReductionSource.{u, u} l E T) (.up ℤ))
    (DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))
  let e' : b.D ≅ G := FF.preimageIso e
  have he (P : CochainComplex (WeilConjectures.scalarReductionSource.{u, u} l E T) ℤ) :
      e'.hom.app (DerivedCategory.Q.obj P) ≫ comp.hom.app P =
        b.cone_factor.hom.app P ≫ DerivedCategory.Q.map ((ellConeIso l E T n).hom.app P) := by
    have h : e'.hom.app (DerivedCategory.Q.obj P) = e.hom.app P :=
      NatTrans.congr_app (FF.map_preimage e.hom) P
    rw [h]
    dsimp only [e, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
    simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  let V := (spCompletedEllRestriction l E T n).mapDerivedCategory
  let v0 : DerivedCategory.Q ⋙ b.V ≅ DerivedCategory.Q ⋙ V :=
    b.restriction_factor ≪≫
      (spCompletedEllRestriction l E T n).mapDerivedCategoryFactors.symm
  let FV := Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso (Scheme.proEtaleRingModules T
        (Scheme.proEtaleConstantRing T (Padic.coefficientExtensionIntegers l E ⧸
          spEllIdeal l E ^ (n + 1)))) (.up ℤ))
    (DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))
  let v : b.V ≅ V := FV.preimageIso v0
  have hv (N : CochainComplex (Scheme.proEtaleRingModules T
        (Scheme.proEtaleConstantRing T (Padic.coefficientExtensionIntegers l E ⧸
          spEllIdeal l E ^ (n + 1)))) ℤ) :
      v.hom.app (DerivedCategory.Q.obj N) = b.restriction_factor.hom.app N ≫
        (spCompletedEllRestriction l E T n).mapDerivedCategoryFactors.inv.app N := by
    have h : v.hom.app (DerivedCategory.Q.obj N) = v0.hom.app N :=
      NatTrans.congr_app (FV.map_preimage v0.hom) N
    rw [h]
    rfl
  let ba : d.T ⊣ V := b.adjunction.ofNatIsoRight v
  let k := adj.leftAdjointUniq ba
  let A : (D.scalar (spCompletedEllCommProjection l E T n)).model.T ⋙ V ≅ G :=
    Functor.isoWhiskerRight k V ≪≫
      (b.A ≪≫ Functor.isoWhiskerLeft d.T v).symm ≪≫ e'
  refine ⟨A, ?_⟩
  intro P N f hf
  have hreg : (SheafOfModules.RegularQuotientCone.complexScalar
      (WeilConjectures.completedIntegralCommRingSheafUnrestricted.{u, u} l E T)
      (ellPowerSection l E T n)).app P ≫
        f = 0 := by
    rw [ellPowerScalar l E T n P]
    exact hf
  let z := CochainComplex.mappingCone.desc
    ((l : ℤ) ^ (n + 1) • 𝟙 P) 0 f (by simp [hf])
  let z' := CochainComplex.mappingCone.desc
    ((SheafOfModules.RegularQuotientCone.complexScalar
      (WeilConjectures.completedIntegralCommRingSheafUnrestricted.{u, u} l E T)
      (ellPowerSection l E T n)).app P)
      0 f (by simp [hreg])
  have hz : (ellConeIso l E T n).hom.app P ≫ z = z' := by
    simpa [ellConeIso, z, z', SheafOfModules.RegularQuotientCone.cone] using
      map_desc_eq (ellPowerScalar l E T n P) f hf
  let a : DerivedCategory.Q.obj P ⟶ V.obj (DerivedCategory.Q.obj N) :=
    DerivedCategory.Q.map f ≫
    (spCompletedEllRestriction l E T n).mapDerivedCategoryFactors.inv.app N
  have hai : a ≫ v.inv.app (DerivedCategory.Q.obj N) =
      DerivedCategory.Q.map f ≫ b.restriction_factor.inv.app N := by
    have hi := inverse_factor (b.restriction_factor.app N)
      ((spCompletedEllRestriction l E T n).mapDerivedCategoryFactors.app N).symm
      (v.app (DerivedCategory.Q.obj N)) (hv N)
    exact (Category.assoc _ _ _).trans (congrArg (fun z ↦ DerivedCategory.Q.map f ≫ z) hi)
  have hb := SheafOfModules.RegularQuotientCone.augmentation_adjoint
    φ (ellPowerSection l E T n) d b P N f hreg
  change V.map ((adj.homEquiv _ _).symm a) =
    A.hom.app (DerivedCategory.Q.obj P) ≫ comp.hom.app P ≫
      DerivedCategory.Q.map z ≫
      (spCompletedEllRestriction l E T n).mapDerivedCategoryFactors.inv.app N
  have hr : b.restriction_factor.inv.app N ≫ v.hom.app (DerivedCategory.Q.obj N) =
      (spCompletedEllRestriction l E T n).mapDerivedCategoryFactors.inv.app N :=
    inv_hom_factor (b.restriction_factor.app N)
      ((spCompletedEllRestriction l E T n).mapDerivedCategoryFactors.app N).symm
      (v.app (DerivedCategory.Q.obj N)) (hv N)
  let Q : CochainComplex (WeilConjectures.scalarReductionSource.{u, u} l E T) ℤ ⥤
      DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T) := DerivedCategory.Q
  have hmap : Q.map ((ellConeIso l E T n).hom.app P) ≫ Q.map z = Q.map z' :=
    (Q.map_comp _ _).symm.trans (congrArg (fun w ↦ Q.map w) hz)
  have hc : e'.hom.app (DerivedCategory.Q.obj P) ≫
      (comp.hom.app P ≫ DerivedCategory.Q.map z ≫
        (spCompletedEllRestriction l E T n).mapDerivedCategoryFactors.inv.app N) =
      (b.cone_factor.hom.app P ≫ DerivedCategory.Q.map z' ≫
        b.restriction_factor.inv.app N) ≫ v.hom.app (DerivedCategory.Q.obj N) :=
    composition_comparison (e'.hom.app (DerivedCategory.Q.obj P)) (comp.hom.app P)
      (b.cone_factor.hom.app P) (Q.map ((ellConeIso l E T n).hom.app P))
      (Q.map z) (Q.map z') (b.restriction_factor.inv.app N)
      (v.hom.app (DerivedCategory.Q.obj N))
      ((spCompletedEllRestriction l E T n).mapDerivedCategoryFactors.inv.app N)
      (he P) hmap hr
  exact comparison_formula adj b.adjunction v b.A e'
    (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj N) a
    (DerivedCategory.Q.map f ≫ b.restriction_factor.inv.app N)
    (b.cone_factor.hom.app P ≫ DerivedCategory.Q.map z' ≫ b.restriction_factor.inv.app N)
    (comp.hom.app P ≫ DerivedCategory.Q.map z ≫
      (spCompletedEllRestriction l E T n).mapDerivedCategoryFactors.inv.app N)
    hai hb hc

private theorem roosConeExists
    {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ i : ℤ, (shiftFunctor C i).Additive] [CategoryTheory.Pretriangulated C]
    {V : ℕ → C} [HasProduct V] (f : ∀ j, V (j + 1) ⟶ V j)
    (M : C) (p : M ⟶ ∏ᶜ V) (δ : (∏ᶜ V) ⟶ M⟦(1 : ℤ)⟧)
    (h : IsDerivedLimitTriangle f M p δ) :
    ∃ q : (Functor.const ℕᵒᵖ).obj M ⟶ Functor.ofOpSequence f,
      CategoryTheory.Pretriangulated.IsHomotopyLimit (Cone.mk M q) ∧
      ∀ j, q.app (op j) = p ≫ Pi.π V j := by
  let F := Functor.ofOpSequence f
  let P : Fan (fun j : ℕ ↦ F.obj (op j)) := Fan.mk _ (Pi.π V)
  let hp : IsLimit P := productIsProduct V
  have ht : CategoryTheory.Pretriangulated.towerShift (F := F) hp =
      towerProductShift f := by
    apply (towerProductShift_eq_iff f _).2
    intro j
    simpa only [P, fan_mk_proj, F, Functor.ofOpSequence_map_homOfLE_succ] using
      CategoryTheory.Pretriangulated.towerShift_proj hp j
  have hT : CategoryTheory.Pretriangulated.Triangle.mk p
      (𝟙 _ - CategoryTheory.Pretriangulated.towerShift (F := F) hp) δ ∈
      distTriang C := by
    rw [ht]
    exact h
  exact ⟨(CategoryTheory.Pretriangulated.coneOfComp hp p
      (CategoryTheory.Pretriangulated.comp_towerShift_of_distinguished hp hT)).π,
    CategoryTheory.Pretriangulated.isHomotopyLimit_coneOfComp hp hT, fun j ↦ rfl⟩

private theorem zeroSandwich
    {C : Type*} [Category C] [HasZeroMorphisms C] {P K I Z W : C}
    (a : P ⟶ K) (b : K ⟶ I) (c : I ⟶ Z) (d : Z ⟶ W) (h : b ≫ c = 0) :
    a ≫ b ≫ c ≫ d = 0 := by
  rw [← Category.assoc b c d, h, zero_comp, comp_zero]

private theorem coneCokernelDesc
    {C : Type*} [Category C] [Abelian C]
    (a : Arrow (CochainComplex C ℤ)) {N : CochainComplex C ℤ}
    (g : (CochainComplex.ConeCoimage.coker.obj a) ⟶ N)
    (f : a.right ⟶ N) (hf : a.hom ≫ f = 0) (hg : cokernel.π a.hom ≫ g = f) :
    CochainComplex.ConeCoimage.ρ.app a ≫ CochainComplex.ConeCoimage.desc.app a ≫ g =
      CochainComplex.mappingCone.desc a.hom 0 f (by simp [hf]) := by
  apply HomologicalComplex.hom_ext
  intro q
  apply CochainComplex.mappingCone.ext_from _ (q + 1) q rfl
  · simp only [HomologicalComplex.comp_f, ← Category.assoc]
    rw [CochainComplex.ConeCoimage.inl_v_ρ_app_f]
    simp only [Category.assoc, CochainComplex.mappingCone.inl_v_desc_f,
      CochainComplex.HomComplex.Cochain.zero_v]
    change (Abelian.coimage.π a.hom).f (q + 1) ≫
      (CochainComplex.mappingCone.inl (CochainComplex.ConeCoimage.cokerSequence a).f).v
        (q + 1) q (by omega) ≫
      (CochainComplex.mappingCone.descShortComplex
        (CochainComplex.ConeCoimage.cokerSequence a)).f q ≫ g.f q = 0
    exact zeroSandwich _ _ _ _
      (CochainComplex.mappingCone.inl_v_descShortComplex_f
        (CochainComplex.ConeCoimage.cokerSequence a) (q + 1) q (by omega))
  · have h := congrArg (· ≫ g) (CochainComplex.ConeCoimage.inr_ρ_desc a)
    simpa only [HomologicalComplex.comp_f, Category.assoc,
      CochainComplex.mappingCone.inr_f_desc_f] using
      congrArg (fun z ↦ z.f q) (h.trans hg)

private theorem appendLast
    {C : Type*} [Category C] {P K I Z W : C}
    (a : P ⟶ K) (b : K ⟶ I) (c : I ⟶ Z) (d : Z ⟶ W) :
    a ≫ b ≫ c ≫ d = (a ≫ b ≫ c) ≫ d := by
  simp only [Category.assoc]

private theorem mapCompositeTarget
    {C B : Type*} [Category C] [Category B] (Q : C ⥤ B)
    {P K I : C} {Z Y : B} (a : P ⟶ K) (i : K ⟶ I)
    (r : Q.obj I ⟶ Z) (v : Z ⟶ Y) (z : Q.obj K ⟶ Y)
    (h : z = Q.map i ≫ r ≫ v) :
    Q.map a ≫ z = (Q.map (a ≫ i) ≫ r) ≫ v := by
  rw [h, Q.map_comp]
  simp only [Category.assoc]

private theorem rightAdjointTransport
    {C B : Type*} [Category C] [Category B] {L : C ⥤ B} {R : B ⥤ C}
    (adj : L ⊣ R) {G : C ⥤ C} (A : L ⋙ R ≅ G)
    {P K : C} {N Y : B} (f : P ⟶ R.obj N) (d : G.obj P ⟶ K)
    (g : K ⟶ R.obj N)
    (h : R.map ((adj.homEquiv P N).symm f) = A.hom.app P ≫ d ≫ g)
    (v : N ⟶ Y) (u : K ⟶ R.obj Y) (hu : u = g ≫ R.map v)
    (k : P ⟶ R.obj Y) (hk : k = f ≫ R.map v) :
    R.map ((adj.homEquiv P Y).symm k) = A.hom.app P ≫ d ≫ u := by
  rw [hk, adj.homEquiv_naturality_right_symm, Functor.map_comp, h, hu]
  simp only [Category.assoc]

private theorem adjointProjectionTransport
    {C B : Type*} [Category C] [Category B] {L : C ⥤ B} {R : B ⥤ C}
    (adj : L ⊣ R) {G : C ⥤ C} (A : L ⋙ R ≅ G)
    {M N : C} (e : M ⟶ N) {Y : B} (f : N ⟶ R.obj Y)
    (g : G.obj N ⟶ R.obj Y)
    (h : R.map ((adj.homEquiv N Y).symm f) = A.hom.app N ≫ g)
    (fM : M ⟶ R.obj Y) (hf : e ≫ f = fM) :
    R.map ((adj.homEquiv M Y).symm fM) =
      A.hom.app M ≫ G.map e ≫ g := by
  rw [← hf, adj.homEquiv_naturality_left_symm, Functor.map_comp, h]
  simpa only [Functor.comp_map, Category.assoc] using
    congrArg (fun z ↦ z ≫ g) (A.hom.naturality e)

private theorem factorThroughCone
    {C B : Type*} [Category C] [Category B] (Q : C ⥤ B)
    {P K I : C} {J M Z : B} (a : P ⟶ K) (i : K ⟶ I) (f : P ⟶ I)
    (h : f = a ≫ i) (w : M ⟶ J) (b : J ⟶ Q.obj P) (r : Q.obj I ⟶ Z) :
    w ≫ b ≫ Q.map f ≫ r = w ≫ (b ≫ Q.map a) ≫ (Q.map i ≫ r) := by
  rw [h, Q.map_comp]
  simp only [Category.assoc]

private theorem isoLeg {C : Type*} [Category C] {X Y Z W : C}
    (e : X ≅ Y) (q : X ⟶ Z) (r : Y ⟶ W) (i : W ≅ Z)
    (h : e.hom ≫ r = q ≫ i.inv) : e.hom ≫ r ≫ i.hom = q := by
  rw [← Category.assoc, h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The two-term free ell^(m+1) resolution identifies the finite reduction of a
specified Roos limit with the limit of the multiplication cones, retaining its
projection. Source: blueprint sk-lem-sp-tower.proof.md, Koszul--Roos comparison;
Stacks 06YY and 0941. (blueprint: lem-sp-tower-bounded-free-cone-comparison).

Proof: transport the given Roos triangle along the level isomorphisms and their
product, using successor compatibility. Removing the first m+1 terms preserves the
homotopy limit and its later projections. The bounded free resolution
[R --ell^(m+1)--> R] of the finite quotient commutes with products and the Roos cone:
only finite sums and two terms occur in each degree. Its tensor with U is the tower
of multiplication cones. This gives the homotopy-limit cone and the comparison a.
The augmentation from each multiplication cone to its cokernel and then to U_(m+1)
is rho followed by desc followed by cokerDesc. The finite complex N and its compatible
level identification fix the finite action. The tensor unit and counit formulas
identify the restriction of the specified adjunct with this augmentation, composed
with a and eU_m. This is a comparison of maps, with no assertion of invertibility;
that follows separately from the normalized adic tower theorem. -/
theorem spTower_bounded_free_cone_comparison
    (C : spDerivedCoefficientTowers l E T D)
    (M : DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))
    [HasProduct (fun n : ℕ ↦ (spDerivedCompletedEvaluation l E T D n).obj C)]
    (p : M ⟶ ∏ᶜ fun n : ℕ ↦ (spDerivedCompletedEvaluation l E T D n).obj C)
    (δ : (∏ᶜ fun n : ℕ ↦ (spDerivedCompletedEvaluation l E T D n).obj C) ⟶ M⟦(1 : ℤ)⟧)
    (hlim : IsDerivedLimitTriangle
      (fun n : ℕ ↦ (spDerivedCompletedTransition l E T D n).app C) M p δ)
    (m : ℕ)
    [HasLimitsOfShape (Discrete ℕ)
      (DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))]
    (U : ℕᵒᵖ ⥤ CochainComplex
      (WeilConjectures.scalarReductionSource.{u, u} l E T) ℤ)
    (hU : CochainComplex.IsNormalizedAdicTower (l : ℤ) U)
    (eU : ∀ j : ℕ, DerivedCategory.Q.obj (U.obj (op (j + 1))) ≅
      (spDerivedCompletedEvaluation l E T D j).obj C)
    (heU : ∀ j : ℕ,
      DerivedCategory.Q.map (U.map
          (homOfLE (Nat.succ_le_succ j.le_succ)).op) ≫ (eU j).hom =
        (eU (j + 1)).hom ≫ (spDerivedCompletedTransition l E T D j).app C)
    (N : CochainComplex (Scheme.proEtaleRingModules T
      (Scheme.proEtaleConstantRing T (Padic.coefficientExtensionIntegers l E ⧸
        spEllIdeal l E ^ (m + 1)))) ℤ)
    (iN : U.obj (op (m + 1)) ≅
      ((spCompletedEllRestriction l E T m).mapHomologicalComplex (.up ℤ)).obj N)
    (eN : DerivedCategory.Q.obj N ≅ (spDerivedCoefficientEvaluation l E T D m).obj C)
    (hN : (eU m).hom = DerivedCategory.Q.map iN.hom ≫
      (spCompletedEllRestriction l E T m).mapDerivedCategoryFactors.inv.app N ≫
      (spCompletedEllRestriction l E T m).mapDerivedCategory.map eN.hom) :
    ∃ (c : Cone (CochainComplex.IsNormalizedAdicTower.arrowTower
      (ϖ := (l : ℤ)) (T := U) (m + 1) ⋙
        CochainComplex.ConeCoimage.cone ⋙ DerivedCategory.Q)),
      CategoryTheory.Pretriangulated.IsHomotopyLimit c ∧
      ∃ (a : (spCompletedEllRestriction l E T m).mapDerivedCategory.obj
            ((D.scalar (spCompletedEllCommProjection l E T m)).model.T.obj M) ≅ c.pt),
        (spCompletedEllRestriction l E T m).mapDerivedCategory.map
            (spTowerReconstructionMap l E T D C M p m) =
          a.hom ≫ c.π.app (op 0) ≫ DerivedCategory.Q.map
            (CochainComplex.ConeCoimage.ρ.app _ ≫ CochainComplex.ConeCoimage.desc.app _ ≫
              hU.cokerDesc (m + 1) (op 0)) ≫ (eU m).hom := by
  let F := U ⋙ DerivedCategory.Q
  obtain ⟨cU, hcU⟩ := CategoryTheory.Pretriangulated.exists_isHomotopyLimit F
  obtain ⟨q, hcM, hp⟩ := roosConeExists
    (fun j : ℕ ↦ (spDerivedCompletedTransition l E T D j).app C) M p δ hlim
  let V : ℕᵒᵖ ⥤ DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T) :=
    Functor.ofOpSequence (X := fun j : ℕ ↦
      (spDerivedCompletedEvaluation l E T D j).obj C)
      (fun j : ℕ ↦ (spDerivedCompletedTransition l E T D j).app C)
  let eVhom : (CategoryTheory.Pretriangulated.addOpFunctor 1 ⋙ F) ⟶ V :=
    NatTrans.ofOpSequence (fun j ↦ (eU j).hom) (by
      intro j
      dsimp only [F, V, Functor.comp_map]
      rw [Functor.ofOpSequence_map_homOfLE_succ]
      have hm : (CategoryTheory.Pretriangulated.addOpFunctor 1).map
          (homOfLE j.le_succ).op = (homOfLE (Nat.succ_le_succ j.le_succ)).op :=
        Subsingleton.elim _ _
      rw [hm]
      exact heU j)
  let eV : (CategoryTheory.Pretriangulated.addOpFunctor 1 ⋙ F) ≅ V :=
    NatIso.ofComponents (fun j ↦ eU j.unop) (by
      intro i j f
      exact eVhom.naturality f)
  obtain ⟨e, hb⟩ := hcM.exists_iso_of_iso eV.symm (hcU.whiskerAdd 1)
  have he (j : ℕ) : e.hom ≫ cU.π.app (op (j + 1)) ≫ (eU j).hom =
      p ≫ Pi.π _ j := by
    have hbj := hb j
    change e.hom ≫ cU.π.app (op (j + 1)) = q.app (op j) ≫ (eU j).inv at hbj
    exact (isoLeg e (q.app (op j)) (cU.π.app (op (j + 1))) (eU j) hbj).trans (hp j)
  let G := CochainComplex.LinearScalarCone.derived
    (A := WeilConjectures.scalarReductionSource.{u, u} l E T) ((l : ℤ) ^ (m + 1))
  obtain ⟨hshift, htri, hprod⟩ := CochainComplex.LinearScalarCone.exact_products
    (A := WeilConjectures.scalarReductionSource.{u, u} l E T) ((l : ℤ) ^ (m + 1))
  let _ := hshift
  let _ := htri
  let _ := hprod
  let c0 := G.mapCone (cU.whisker (CategoryTheory.Pretriangulated.addOpFunctor (m + 1)))
  have hc0 : CategoryTheory.Pretriangulated.IsHomotopyLimit c0 :=
    (hcU.whiskerAdd (m + 1)).map G
  let K := CochainComplex.IsNormalizedAdicTower.arrowTower
    (ϖ := (l : ℤ)) (T := U) (m + 1) ⋙
      CochainComplex.ConeCoimage.cone ⋙ DerivedCategory.Q
  let w : (CategoryTheory.Pretriangulated.addOpFunctor (m + 1) ⋙ F) ⋙ G ≅ K :=
    Functor.isoWhiskerLeft
      (CategoryTheory.Pretriangulated.addOpFunctor (m + 1) ⋙ U)
      (CochainComplex.LinearScalarCone.comparison ((l : ℤ) ^ (m + 1)))
  let c : Cone K := { pt := c0.pt, π := c0.π ≫ w.hom }
  have hcl : CategoryTheory.Pretriangulated.IsHomotopyLimit c :=
    hc0.of_iso w c (Iso.refl _) (fun j ↦ by simp [c])
  let adj := (D.scalar (spCompletedEllCommProjection l E T m)).adjunction
  obtain ⟨A, hA⟩ := strictCoefficientAdjoint l E T D m
  let Q := DerivedCategory.Q (C := WeilConjectures.scalarReductionSource.{u, u} l E T)
  let k := (CategoryTheory.Pretriangulated.addOpFunctor (m + 1)).obj (op 0)
  let P := U.obj k
  let red : P ⟶ U.obj (op (m + 1)) :=
    (CochainComplex.IsNormalizedAdicTower.red (T := U) (m + 1)).app (op 0)
  let aug := CochainComplex.LinearScalarCone.augmentation hU (m + 1) (op 0)
  let comp := CochainComplex.LinearScalarCone.comparison
    (A := WeilConjectures.scalarReductionSource.{u, u} l E T)
    ((l : ℤ) ^ (m + 1))
  let Vd := (spCompletedEllRestriction l E T m).mapDerivedCategory
  let r := (spCompletedEllRestriction l E T m).mapDerivedCategoryFactors.inv.app N
  let f : P ⟶ ((spCompletedEllRestriction l E T m).mapHomologicalComplex
      (.up ℤ)).obj N := red ≫ iN.hom
  have hf : ((l : ℤ) ^ (m + 1) • 𝟙 P) ≫ f = 0 := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ iN.hom) (hU.smul_comp_red (m + 1) (op 0))).trans (zero_comp))
  have hlevel := hA P N f hf
  have hdesc : CochainComplex.mappingCone.desc
      ((l : ℤ) ^ (m + 1) • 𝟙 P) 0 f (by simp [hf]) =
      aug ≫ iN.hom := by
    have hred : cokernel.π
        ((CochainComplex.IsNormalizedAdicTower.arrowTower
          (ϖ := (l : ℤ)) (T := U) (m + 1)).obj (op 0)).hom ≫
        (hU.cokerDesc (m + 1) (op 0) ≫ iN.hom) = f :=
      (Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ iN.hom) (hU.π_cokerDesc (m + 1) (op 0)))
    have h := coneCokernelDesc
      ((CochainComplex.IsNormalizedAdicTower.arrowTower
        (ϖ := (l : ℤ)) (T := U) (m + 1)).obj (op 0))
      (hU.cokerDesc (m + 1) (op 0) ≫ iN.hom) f hf hred
    exact h.symm.trans (appendLast _ _ _ _)
  let d : G.obj (Q.obj P) ⟶ Q.obj (U.obj (op (m + 1))) :=
    comp.hom.app P ≫ Q.map aug
  have hbase : Vd.map ((adj.homEquiv (Q.obj P) (DerivedCategory.Q.obj N)).symm
      (Q.map f ≫ r)) =
      A.hom.app (Q.obj P) ≫ d ≫ (Q.map iN.hom ≫ r) :=
    hlevel.trans (factorThroughCone Q aug iN.hom _ hdesc (A.hom.app (Q.obj P))
      (comp.hom.app P) r)
  let eLevel : Q.obj P ⟶ Vd.obj ((spDerivedCoefficientEvaluation l E T D m).obj C) :=
    Q.map red ≫ (eU m).hom
  have heLevel : eLevel = (Q.map f ≫ r) ≫ Vd.map eN.hom :=
    mapCompositeTarget Q red iN.hom r (Vd.map eN.hom)
      ((eU m).hom) hN
  have hb : Vd.map ((adj.homEquiv (Q.obj P)
      ((spDerivedCoefficientEvaluation l E T D m).obj C)).symm eLevel) =
      A.hom.app (Q.obj P) ≫ d ≫ (eU m).hom := by
    have hu : (eU m).hom =
        (Q.map iN.hom ≫ r) ≫ Vd.map eN.hom :=
      hN.trans (Category.assoc _ _ _).symm
    exact rightAdjointTransport adj A (Q.map f ≫ r) d (Q.map iN.hom ≫ r)
      hbase eN.hom ((eU m).hom) hu eLevel heLevel
  let fM : cU.pt ⟶ Vd.obj ((spDerivedCoefficientEvaluation l E T D m).obj C) :=
    cU.π.app (op (m + 1)) ≫ (eU m).hom
  have hp : cU.π.app k ≫ eLevel = fM := by
    have hn : cU.π.app k ≫ Q.map red = cU.π.app (op (m + 1)) :=
      cU.w (homOfLE (Nat.le_add_left (m + 1) 0)).op
    simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ (eU m).hom) hn
  have hcanonical : Vd.map ((adj.homEquiv cU.pt
      ((spDerivedCoefficientEvaluation l E T D m).obj C)).symm fM) =
      A.hom.app cU.pt ≫ G.map (cU.π.app k) ≫ d ≫ (eU m).hom := by
    exact adjointProjectionTransport adj A (cU.π.app k) eLevel
      (d ≫ (eU m).hom) hb fM hp
  let a : (spCompletedEllRestriction l E T m).mapDerivedCategory.obj
      ((D.scalar (spCompletedEllCommProjection l E T m)).model.T.obj M) ≅ c.pt :=
    A.app M ≪≫ G.mapIso e
  refine ⟨c, hcl, a, ?_⟩
  have hfM : e.hom ≫ fM = p ≫ Pi.π _ m := by
    exact he m
  have hfinal := adjointProjectionTransport adj A e.hom fM
    (G.map (cU.π.app k) ≫ d ≫ (eU m).hom) hcanonical
    (p ≫ Pi.π _ m) hfM
  simpa only [spTowerReconstructionMap, a, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, c, c0, w, NatTrans.comp_app, Functor.mapCone_π_app,
    Cone.whisker_π, Functor.whiskerLeft_app, Functor.isoWhiskerLeft_hom,
    d, comp, aug, G, k, P, Q, adj, CochainComplex.LinearScalarCone.augmentation,
    Category.assoc, Functor.comp_obj] using hfinal

end AlgebraicGeometry.ProEtale
