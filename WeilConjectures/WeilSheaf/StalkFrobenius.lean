/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.StalkFunctor

/-!
# The Frobenius of the geometric stalks of Weil sheaves
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry.WeilSheaf

open scoped AlgebraicGeometry.ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]

section GlobalSections


/-- The global sections of `(e¹)⁻¹_* N` and of `(e⁻¹)_* N` are identified compatibly with the
identification `(e¹)⁻¹_* N ≅ (e⁻¹)_* (e⁰)⁻¹_* N ≅ (e⁻¹)_* N` defining the first iterate of a
Weil structure. -/
private lemma globalSectionsLowerStarIso_inv_comp_pow_one {Y : Scheme.{u}} (e : Aut Y)
    (N : Sheaf (Scheme.ProEt.topology Y) (WeilCoefficients.{u} l)) (h₀ : (e ^ 0).inv = 𝟙 Y)
    (h₁ : (e ^ 1).inv = (e ^ 0).inv ≫ e.inv) :
    (ProEtale.globalSectionsLowerStarIso _ (e ^ 1).inv).inv.app N ≫
      (Sheaf.Γ _ _).map ((ProEtale.lowerStarCongr _ h₁).hom.app N ≫
          (ProEtale.lowerStarComp _ (e ^ 0).inv e.inv).inv.app N ≫
          (e.inv)_*[_].map ((ProEtale.lowerStarCongr _ h₀).hom.app N ≫
            (ProEtale.lowerStarId _ Y).hom.app N)) =
    (ProEtale.globalSectionsLowerStarIso _ e.inv).inv.app N := by
  have e₀ := ProEtale.globalSectionsLowerStarIso_congr (WeilCoefficients.{u} l) h₀ N
  rw [ProEtale.globalSectionsLowerStarIso_id] at e₀
  have e₁ := ProEtale.globalSectionsLowerStarIso_congr (WeilCoefficients.{u} l) h₁ N
  have e₂ := ProEtale.globalSectionsLowerStarIso_comp (WeilCoefficients.{u} l) (e ^ 0).inv
    e.inv N
  have e₃ := (ProEtale.globalSectionsLowerStarIso (WeilCoefficients.{u} l) e.inv).hom.naturality
    ((ProEtale.lowerStarCongr _ h₀).hom.app N ≫ (ProEtale.lowerStarId _ _).hom.app N)
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc, Functor.id_obj] at e₃
  rw [← cancel_mono ((ProEtale.globalSectionsLowerStarIso _ e.inv).hom.app N)]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app]
  rw [e₃, e₀, ← e₂]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [e₁, Iso.inv_hom_id_app]

variable (F : WeilSheaf k₀ l X)

/-- The first iterate `φ₁ : (Fr¹)^* F ≅ F` of the Weil structure, on the underlying sheaves. -/
lemma forget_map_frobeniusPowIso_one_hom
    (h₀ : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).inv = 𝟙 _)
    (h₁ : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 1).inv =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).inv ≫
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv) :
    (ProEtale.AdicSheaf.forget _).map (F.frobeniusPowIso 1).hom =
      (ProEtale.lowerStarCongr _ h₁).hom.app F.obj.carrier.X ≫
        (ProEtale.lowerStarComp _
          ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).inv
          (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).inv.app F.obj.carrier.X ≫
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv)_*[_].map
          ((ProEtale.lowerStarCongr _ h₀).hom.app F.obj.carrier.X ≫
            (ProEtale.lowerStarId _ _).hom.app F.obj.carrier.X) ≫
        (ProEtale.AdicSheaf.forget _).map F.obj.str.hom := by
  simp only [frobeniusPowIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom, Functor.mapIso_hom,
    Functor.map_comp, ProEtale.adicLowerStarId, NatIso.trans_app, Category.assoc]
  rfl

/-- The Frobenius of the global sections through the first iterate `φ₁` of the Weil structure
is the Frobenius through `φ`. -/
lemma globalSectionsLowerStarIso_inv_comp_frobeniusPowIso_one :
    (ProEtale.globalSectionsLowerStarIso _
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 1).inv).inv.app
          F.obj.carrier.X ≫
      (Sheaf.Γ _ _).map ((ProEtale.AdicSheaf.forget _).map (F.frobeniusPowIso 1).hom) =
    (ProEtale.globalSectionsLowerStarIso _
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).inv.app F.obj.carrier.X ≫
      (Sheaf.Γ _ _).map ((ProEtale.AdicSheaf.forget _).map F.obj.str.hom) := by
  have h₀ : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).inv = 𝟙 _ := by
    rw [pow_zero]; rfl
  have h₁ : ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 1).inv =
      ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 0).inv ≫
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv := by
    rw [pow_succ, Aut.Aut_mul_def, Iso.trans_inv]
  rw [forget_map_frobeniusPowIso_one_hom F h₀ h₁,
    ← globalSectionsLowerStarIso_inv_comp_pow_one _ _ h₀ h₁]
  simp only [Functor.map_comp, Category.assoc]

variable (s : Spec (.of (AlgebraicClosure k₀)) ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)

lemma globalSectionsToStalkObj_eq :
    F.globalSectionsToStalkObj s =
      (ProEtale.globalSectionsToUpperStar _ s).app F.obj.carrier.X :=
  rfl

/-- Restricting global sections to the stalk at `s` and then passing to the stalk at the
reparametrisation `σᵐ ≫ s` is restricting to the stalk at `σᵐ ≫ s`. -/
lemma globalSectionsToStalkObj_comp_stalkObjSpecFrobeniusPowIso_inv (m : ℕ) :
    F.globalSectionsToStalkObj s ≫ (F.stalkObjSpecFrobeniusPowIso m s).inv =
      F.globalSectionsToStalkObj ((specGeometricFrobenius k₀ ^ m).hom ≫ s) := by
  rw [Iso.comp_inv_eq, globalSectionsToStalkObj_eq, globalSectionsToStalkObj_eq]
  have h := ProEtale.globalSectionsToUpperStar_comp _ (specGeometricFrobenius k₀ ^ m).hom s
    F.obj.carrier.X
  simp only [stalkObjSpecFrobeniusPowIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    reassoc_of% h, ProEtale.globalSectionsToUpperStar_app_comp_globalSectionsUpperStarIso,
    Category.comp_id]

/-- Restriction of global sections to equal geometric points. -/
lemma globalSectionsToStalkObj_comp_eqToHom {t t' : Spec (.of (AlgebraicClosure k₀)) ⟶
    (X ↘ Spec (CommRingCat.of k₀)).geometricFiber} (h : t = t') :
    F.globalSectionsToStalkObj t ≫ eqToHom (congrArg F.stalkObj h) =
      F.globalSectionsToStalkObj t' := by
  subst h
  simp

/-- Restricting global sections to the stalk at `s ≫ Frᵐ` and transporting to the stalk at `s`
along the Weil structure is restricting the image of the sections under `φ_m`. -/
lemma globalSectionsToStalkObj_comp_stalkObjFrobeniusPowIso_hom (m : ℕ) :
    F.globalSectionsToStalkObj
        (s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom) ≫
      (F.stalkObjFrobeniusPowIso m s).hom =
    (ProEtale.globalSectionsLowerStarIso _
        ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).inv).inv.app
          F.obj.carrier.X ≫
      (Sheaf.Γ _ _).map ((ProEtale.AdicSheaf.forget _).map (F.frobeniusPowIso m).hom) ≫
      F.globalSectionsToStalkObj s := by
  rw [globalSectionsToStalkObj_eq, globalSectionsToStalkObj_eq]
  have h := ProEtale.globalSectionsToUpperStar_comp _ s
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom F.obj.carrier.X
  have h' := ProEtale.globalSectionsToUpperStar_app_comp_globalSectionsUpperStarIso
    (WeilCoefficients.{u} l) ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m)
      F.obj.carrier.X
  simp only [ProEtale.globalSectionsUpperStarIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app] at h'
  rw [← Category.assoc] at h'
  replace h' := (Iso.comp_hom_eq_id ((ProEtale.globalSectionsLowerStarIso _
    ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).inv).app _)).1 h'
  simp only [stalkObjFrobeniusPowIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Functor.map_comp, reassoc_of% h]
  have nat {A B : Sheaf (Scheme.ProEt.topology (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
      (WeilCoefficients.{u} l)} (f : A ⟶ B) :
      (ProEtale.globalSectionsToUpperStar _ s).app A ≫ (Sheaf.Γ _ _).map ((s)^*[_].map f) =
        (Sheaf.Γ _ _).map f ≫ (ProEtale.globalSectionsToUpperStar _ s).app B :=
    ((ProEtale.globalSectionsToUpperStar _ s).naturality f).symm
  rw [reassoc_of% nat, nat, reassoc_of% h']
  rfl

/-- The restriction of global sections to a stalk intertwines the Frobenius of the global
sections with the Frobenius of the stalk, as morphisms. -/
lemma globalSectionsToStalkObj_comp_stalkAt_iso
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 1).hom =
      (specGeometricFrobenius k₀ ^ 1).hom ≫ s) :
    F.globalSectionsToStalkObj s ≫ ((F.stalkObjSpecFrobeniusPowIso 1 s).symm ≪≫
        eqToIso (congrArg F.stalkObj hs.symm) ≪≫ F.stalkObjFrobeniusPowIso 1 s).hom =
      ((ProEtale.globalSectionsLowerStarIso _
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).symm.app F.obj.carrier.X ≪≫
        (Sheaf.Γ _ _).mapIso ((ProEtale.AdicSheaf.forget _).mapIso F.obj.str)).hom ≫
      F.globalSectionsToStalkObj s := by
  simp only [Iso.trans_hom, Iso.symm_hom, eqToIso.hom, Iso.app_hom, Functor.mapIso_hom,
    Category.assoc]
  rw [reassoc_of% globalSectionsToStalkObj_comp_stalkObjSpecFrobeniusPowIso_inv,
    reassoc_of% (globalSectionsToStalkObj_comp_eqToHom F hs.symm),
    globalSectionsToStalkObj_comp_stalkObjFrobeniusPowIso_hom,
    reassoc_of% globalSectionsLowerStarIso_inv_comp_frobeniusPowIso_one]

omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] in
private theorem toModuleCat_map_comp_apply {M N P : WeilCoefficients.{u} l} (f : M ⟶ N)
    (g : N ⟶ P) (x : (WeilCoefficients.toModuleCat l).obj M) :
    ((WeilCoefficients.toModuleCat l).map (f ≫ g)).hom x =
      ((WeilCoefficients.toModuleCat l).map g).hom
        (((WeilCoefficients.toModuleCat l).map f).hom x) := by
  rw [Functor.map_comp]
  rfl

omit [Finite k₀] [Fact (ringChar k₀ ≠ l)] in
private theorem linearEquivOfIso_apply {M N : WeilCoefficients.{u} l} (e : M ≅ N)
    (x : (WeilCoefficients.toModuleCat l).obj M) :
    WeilCoefficients.linearEquivOfIso e x = ((WeilCoefficients.toModuleCat l).map e.hom).hom x :=
  rfl

private theorem globalSections_frobenius_eq [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))] :
    F.globalSections.frobenius = WeilCoefficients.linearEquivOfIso
      ((ProEtale.globalSectionsLowerStarIso _
        (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).symm.app F.obj.carrier.X ≪≫
        (Sheaf.Γ _ _).mapIso ((ProEtale.AdicSheaf.forget _).mapIso F.obj.str)) :=
  rfl

private theorem stalkAt_frobenius_eq' (m : ℕ)
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).hom =
      (specGeometricFrobenius k₀ ^ m).hom ≫ s) :
    (F.stalkAt s m hs).frobenius = WeilCoefficients.linearEquivOfIso
      ((F.stalkObjSpecFrobeniusPowIso m s).symm ≪≫ eqToIso (congrArg F.stalkObj hs.symm) ≪≫
        F.stalkObjFrobeniusPowIso m s) :=
  rfl

/-- The restriction of global sections to the stalk at a geometric point `s` with
`s ≫ Fr = σ ≫ s`, for instance a point over a `k₀`-rational point, intertwines the Frobenius of
`Γ(X̄, F)` with the Frobenius of `F_s` relative to `k₀`:

```
          Fr
  Γ(X̄, F) ---> Γ(X̄, F)
     |            |
     v            v
    F_s  -----> F_s
          Fr
```
-/
theorem globalSectionsToStalkObj_frobenius [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    (hs : s ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ 1).hom =
      (specGeometricFrobenius k₀ ^ 1).hom ≫ s)
    (a : F.globalSections.carrier) :
    ((WeilCoefficients.toModuleCat l).map (F.globalSectionsToStalkObj s)).hom
        (F.globalSections.frobenius a) =
      (F.stalkAt s 1 hs).frobenius
        (((WeilCoefficients.toModuleCat l).map (F.globalSectionsToStalkObj s)).hom a) := by
  -- the intermediate equations are stated with explicit arguments to keep the kernel fast
  let eΓ := (ProEtale.globalSectionsLowerStarIso _
    (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius.inv).symm.app F.obj.carrier.X ≪≫
      (Sheaf.Γ _ _).mapIso ((ProEtale.AdicSheaf.forget _).mapIso F.obj.str)
  let es := (F.stalkObjSpecFrobeniusPowIso 1 s).symm ≪≫
    eqToIso (congrArg F.stalkObj hs.symm) ≪≫ F.stalkObjFrobeniusPowIso 1 s
  have h₀ := toModuleCat_map_comp_apply eΓ.hom (F.globalSectionsToStalkObj s) a
  have h₁ := congrArg (fun g ↦ ((WeilCoefficients.toModuleCat l).map g).hom a)
    (globalSectionsToStalkObj_comp_stalkAt_iso F s hs)
  have h₂ := toModuleCat_map_comp_apply (F.globalSectionsToStalkObj s) es.hom a
  have e₁ := (LinearEquiv.congr_fun (globalSections_frobenius_eq F) a).trans
    (linearEquivOfIso_apply eΓ a)
  have e₂ := (LinearEquiv.congr_fun (stalkAt_frobenius_eq' F s 1 hs)
    (((WeilCoefficients.toModuleCat l).map (F.globalSectionsToStalkObj s)).hom a)).trans
      (linearEquivOfIso_apply es
        (((WeilCoefficients.toModuleCat l).map (F.globalSectionsToStalkObj s)).hom a))
  exact (congrArg ((WeilCoefficients.toModuleCat l).map (F.globalSectionsToStalkObj s)).hom
    e₁).trans (h₀.symm.trans (h₁.symm.trans (h₂.trans e₂.symm)))

end GlobalSections


end AlgebraicGeometry.WeilSheaf
