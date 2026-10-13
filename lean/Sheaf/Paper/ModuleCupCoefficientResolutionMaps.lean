/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups U1 and J3
-/
module

public import Sheaf.Paper.ModuleCupResolutionData
import Sheaf.Paper.ModuleCupFlasqueAcyclicity
import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
import Sheaf.Paper.ModuleCupGodementCoefficientComplexes

/-! # Compatible computing resolutions for coefficient morphisms

Source: Stacks Project, Section 20.31 (Tag 0FKU), and the functorial Godement
construction in Section 20.30 (Tag 0FKR).
-/

@[expose] public section

universe v
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

/-- Equip a flasque resolution with a computing injective comparison. -/
private def computingFlasqueResolution {X : Scheme.{v}} {F : X.Modules}
    (K : CochainComplex X.Modules ℕ)
    (a : (CochainComplex.single₀ X.Modules).obj F ⟶ K) [QuasiIso a]
    (hK : ∀ n : ℕ, TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj (K.X n))) :
    CupAcyclicResolution F := by
  let : EnoughInjectives (SheafOfModules.{v} (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  have : PreservesFiniteLimits (RingedSpace.globalSectionsFunctor X.toRingedSpace) := by
    change PreservesFiniteLimits
      (SheafOfModules.evaluation.{v} (moduleRings X.toRingedSpace) (op ⊤))
    infer_instance
  let I := injectiveResolution F
  let φ := InjectiveResolution.descOfQuasiIso (𝟙 F) I a
  have hA : ∀ n, (RingedSpace.globalSectionsFunctor X.toRingedSpace).rightAcyclic
      (K.X n) := by
    intro n q
    have := hK n
    exact moduleCup_flasque_acyclicity X (K.X n) (q + 1) (by omega)
  have := Functor.quasiIso_map_of_rightAcyclic_nat
    (RingedSpace.globalSectionsFunctor X.toRingedSpace) φ hA
      (fun _ ↦ Functor.rightAcyclic_of_injective _)
  exact {
    K := K
    augmentation := a
    quasiIso := inferInstance
    I := I
    comparison := φ
    over := by simp [φ]
    computes := fun n ↦ inferInstance }

private theorem supportedNat {X : Scheme.{v}} (K : CochainComplex X.Modules ℤ)
    [K.IsStrictlyGE 0] : K.IsStrictlySupported ComplexShape.embeddingUpNat := by
  constructor
  intro i hi
  refine K.isZero_of_isStrictlyGE 0 i ?_
  by_contra h
  exact hi i.toNat (by
    change (i.toNat : ℤ) = i
    exact Int.toNat_of_nonneg (by omega))

private theorem restrictionQuasiIso {X : Scheme.{v}}
    {K L : CochainComplex X.Modules ℤ} (f : K ⟶ L) [QuasiIso f]
    [K.IsStrictlyGE 0] [L.IsStrictlyGE 0] :
    QuasiIso (HomologicalComplex.restrictionMap f ComplexShape.embeddingUpNat) := by
  let e := ComplexShape.embeddingUpNat
  have := supportedNat K
  have := supportedNat L
  have : IsIso (K.restrictionToTruncGE' e) :=
    HomologicalComplex.Hom.isIso_of_components _
  have : IsIso (L.restrictionToTruncGE' e) :=
    HomologicalComplex.Hom.isIso_of_components _
  have h : QuasiIso (HomologicalComplex.truncGEMap f e) :=
    (HomologicalComplex.quasiIso_truncGEMap_iff f e).2 (fun _ _ _ ↦ inferInstance)
  have : QuasiIso (HomologicalComplex.truncGE'Map f e) :=
    (HomologicalComplex.quasiIso_extendMap_iff _ e).1 h
  have hcomp : QuasiIso (K.restrictionToTruncGE' e ≫
      HomologicalComplex.truncGE'Map f e) := inferInstance
  rw [HomologicalComplex.restrictionToTruncGE'_naturality] at hcomp
  exact quasiIso_of_comp_right _ (L.restrictionToTruncGE' e)

private def natAugmentation {X : Scheme.{v}} {F : X.Modules}
    {K : CochainComplex X.Modules ℤ}
    (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶ K) :
    (CochainComplex.single₀ X.Modules).obj F ⟶ K.restriction ComplexShape.embeddingUpNat :=
  (CochainComplex.fromSingle₀Equiv _ F).symm ⟨a.f 0, by
    change a.f 0 ≫ K.d 0 1 = 0
    rw [a.comm 0 1]
    simp⟩

private def singleNatIso {X : Scheme.{v}} (F : X.Modules) :
    (CochainComplex.single₀ X.Modules).obj F ≅
      ((CochainComplex.singleFunctor X.Modules 0).obj F).restriction
        ComplexShape.embeddingUpNat := by
  refine HomologicalComplex.Hom.isoOfComponents (fun n ↦ ?_) ?_
  · exact eqToIso (by
      change ((HomologicalComplex.single X.Modules (ComplexShape.up ℕ) 0).obj F).X n =
        ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).obj F).X (n : ℤ)
      by_cases hn : n = 0
      · subst n; rfl
      · simp [HomologicalComplex.single, hn])
  · intro i j hij
    simp [HomologicalComplex.restriction]

private theorem natAugmentation_quasiIso {X : Scheme.{v}} {F : X.Modules}
    {K : CochainComplex X.Modules ℤ}
    (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶ K)
    [QuasiIso a] [K.IsStrictlyGE 0] : QuasiIso (natAugmentation a) := by
  have := restrictionQuasiIso a
  have h : natAugmentation a = (singleNatIso F).hom ≫
      HomologicalComplex.restrictionMap a ComplexShape.embeddingUpNat := by
    apply (CochainComplex.fromSingle₀Equiv _ F).injective
    apply Subtype.ext
    simp [natAugmentation, singleNatIso, HomologicalComplex.restrictionMap,
      ComplexShape.embeddingUpNat]
    rfl
  rw [h]
  infer_instance

private def tensorChainSectionPair {X : Scheme.{v}} [MonoidalPreadditive X.Modules]
    (K L M : CochainComplex X.Modules ℤ)
    (t : HomologicalComplex.tensorObj K L ⟶ M) (r s : ℕ) (V : X.Opens) :
    Γ(K.X (r : ℤ), V) →ₗ[Γ(X, V)] Γ(L.X (s : ℤ), V) →ₗ[Γ(X, V)]
      Γ(M.X ((r + s : ℕ) : ℤ), V) :=
  TensorProduct.curry
    (((HomologicalComplex.ιTensorObj K L (r : ℤ) (s : ℤ) ((r + s : ℕ) : ℤ)
      (by simp) ≫ t.f _).val.app (op V)).hom.comp (tensorSectionsMap _ _ V))

private theorem tensorChainSectionPair_apply {X : Scheme.{v}}
    [MonoidalPreadditive X.Modules]
    (K L M : CochainComplex X.Modules ℤ)
    (t : HomologicalComplex.tensorObj K L ⟶ M) (r s : ℕ) (V : X.Opens)
    (a : Γ(K.X (r : ℤ), V)) (b : Γ(L.X (s : ℤ), V)) :
    tensorChainSectionPair K L M t r s V a b =
      (t.f _).val.app (op V)
        ((HomologicalComplex.ιTensorObj K L (r : ℤ) (s : ℤ) ((r + s : ℕ) : ℤ)
          (by simp)).val.app (op V) (tmulSection a b)) := by
  simp [tensorChainSectionPair, TensorProduct.curry_apply]
  rfl

private theorem app_val_apply {X : Scheme.{v}} {A B : X.Modules}
    (f : A ⟶ B) (V : X.Opens) (z : Γ(A, V)) :
    f.app V z = f.val.app (op V) z := rfl

private theorem tensorSection_restriction {X : Scheme.{v}} {A B C : X.Modules}
    (f : A ⊗ B ⟶ C) (V W : X.Opens) (h : W ≤ V)
    (x : Γ(A, V)) (y : Γ(B, V)) :
    C.presheaf.map (homOfLE h).op (f.app V (tmulSection x y)) =
      f.app W (tmulSection (A.presheaf.map (homOfLE h).op x)
        (B.presheaf.map (homOfLE h).op y)) := by
  rw [← Hom.app_presheaf_map f, tmulSection_map]

private theorem val_id_apply {X : Scheme.{v}} (A : X.Modules)
    (V : X.Opens) (z : Γ(A, V)) : (𝟙 A : A ⟶ A).val.app (op V) z = z := rfl

private theorem tensorChainSectionPair_transport {X : Scheme.{v}}
    [MonoidalPreadditive X.Modules] (K L M : CochainComplex X.Modules ℤ)
    (t : HomologicalComplex.tensorObj K L ⟶ M) (r s n : ℕ) (h : r + s = n)
    (V : X.Opens) (x : Γ(K.X (r : ℤ), V)) (y : Γ(L.X (s : ℤ), V)) :
    (eqToHom (congrArg (fun n : ℕ ↦ M.X (n : ℤ)) h)).val.app (op V)
      (tensorChainSectionPair K L M t r s V x y) =
      (t.f (n : ℤ)).val.app (op V)
        ((HomologicalComplex.ιTensorObj K L (r : ℤ) (s : ℤ) (n : ℤ)
          (by exact_mod_cast h)).val.app (op V) (tmulSection x y)) := by
  subst n
  simpa only [eqToHom_refl, val_id_apply] using
    tensorChainSectionPair_apply K L M t r s V x y

private theorem app_zsmul_apply {X : Scheme.{v}} {A B : X.Modules}
    (n : ℤ) (f : A ⟶ B) (V : X.Opens) (z : Γ(A, V)) :
    (n • f).app V z = n • f.app V z := by
  let e : (A ⟶ B) →+ (Γ(A, V) →+ Γ(B, V)) :=
    { toFun := fun f ↦ (f.app V).hom
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  exact congrArg (fun f : Γ(A, V) →+ Γ(B, V) ↦ f z) (e.map_zsmul n f)

private theorem tensorChain_leibniz {X : Scheme.{v}} [MonoidalPreadditive X.Modules]
    (K L M : CochainComplex X.Modules ℤ)
    (t : HomologicalComplex.tensorObj K L ⟶ M) (p q : ℤ) (V : X.Opens)
    (x : Γ(K.X p, V)) (y : Γ(L.X q, V)) :
    (M.d (p + q) (p + q + 1)).app V
      ((t.f (p + q)).app V
        ((HomologicalComplex.ιTensorObj K L p q (p + q) rfl).app V (tmulSection x y))) =
      (t.f (p + q + 1)).app V
        ((HomologicalComplex.ιTensorObj K L (p + 1) q (p + q + 1) (by omega)).app V
          (tmulSection ((K.d p (p + 1)).app V x) y)) +
      p.negOnePow • (t.f (p + q + 1)).app V
        ((HomologicalComplex.ιTensorObj K L p (q + 1) (p + q + 1) (by omega)).app V
          (tmulSection x ((L.d q (q + 1)).app V y))) := by
  have hd : HomologicalComplex.ιTensorObj K L p q (p + q) rfl ≫
      (HomologicalComplex.tensorObj K L).d (p + q) (p + q + 1) =
      K.d p (p + 1) ▷ L.X q ≫
        HomologicalComplex.ιTensorObj K L (p + 1) q (p + q + 1) (by omega) +
      p.negOnePow • (K.X p ◁ L.d q (q + 1) ≫
        HomologicalComplex.ιTensorObj K L p (q + 1) (p + q + 1) (by omega)) := by
    rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
      HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _
        (rfl : (ComplexShape.up ℤ).Rel p (p + 1)) _ _
        (show p + 1 + q = p + q + 1 by omega),
      HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _
        (rfl : (ComplexShape.up ℤ).Rel q (q + 1)) _
        (show p + (q + 1) = p + q + 1 by omega)]
    simp
  have h := congrArg (fun f ↦ f ≫ t.f (p + q + 1)) hd
  simp only [Units.smul_def, Preadditive.add_comp, Preadditive.zsmul_comp,
    Category.assoc] at h
  rw [← t.comm (p + q) (p + q + 1)] at h
  have hs := congrArg (fun f ↦ f.app V (tmulSection x y)) h
  simpa only [Hom.comp_app, ConcreteCategory.comp_apply, Hom.add_app,
    AddCommGrpCat.hom_add_apply, app_zsmul_apply, whiskerRight_app_tmulSection,
    whiskerLeft_app_tmulSection, Units.smul_def] using hs

/-- Package an augmented flasque tensor-paired complex into computing resolutions. -/
private def computingPairing {X : Scheme.{v}} {F G : X.Modules} [MonoidalPreadditive X.Modules]
    (K L M : CochainComplex X.Modules ℤ)
    (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶ K)
    (b : (CochainComplex.singleFunctor X.Modules 0).obj G ⟶ L)
    (c : (CochainComplex.singleFunctor X.Modules 0).obj (F ⊗ G) ⟶ M)
    (ha : QuasiIso a) (hb : QuasiIso b) (hc : QuasiIso c)
    (hK : K.IsStrictlyGE 0) (hL : L.IsStrictlyGE 0) (hM : M.IsStrictlyGE 0)
    (fK : ∀ n : ℤ, TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj (K.X n)))
    (fL : ∀ n : ℤ, TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj (L.X n)))
    (fM : ∀ n : ℤ, TopCat.Sheaf.IsFlasque
      ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj (M.X n)))
    (t : HomologicalComplex.tensorObj K L ⟶ M)
    (ht : ∀ (V : X.Opens)
      (x : Γ(((CochainComplex.singleFunctor X.Modules 0).obj F).X 0, V))
      (y : Γ(((CochainComplex.singleFunctor X.Modules 0).obj G).X 0, V)),
      (t.f 0).val.app (op V)
        ((HomologicalComplex.ιTensorObj K L 0 0 0 (by simp)).val.app (op V)
          (tmulSection ((a.f 0).val.app (op V) x) ((b.f 0).val.app (op V) y))) =
        (c.f 0).val.app (op V) (tmulSection x y)) :
    CupResolutionPairing F G := by
  have := ha
  have := hb
  have := hc
  have := hK
  have := hL
  have := hM
  have := natAugmentation_quasiIso a
  have := natAugmentation_quasiIso b
  have := natAugmentation_quasiIso c
  refine {
    left := computingFlasqueResolution _ (natAugmentation a) (fun n ↦ fK n)
    right := computingFlasqueResolution _ (natAugmentation b) (fun n ↦ fL n)
    target := computingFlasqueResolution _ (natAugmentation c) (fun n ↦ fM n)
    pair := tensorChainSectionPair K L M t
    restriction := ?_
    leibniz := ?_
    augmentation_pair := ?_ }
  · intro r s V W h x y
    change (M.X ((r + s : ℕ) : ℤ)).presheaf.map (homOfLE h).op
      (tensorChainSectionPair K L M t r s V x y) =
        tensorChainSectionPair K L M t r s W
          ((K.X (r : ℤ)).presheaf.map (homOfLE h).op x)
          ((L.X (s : ℤ)).presheaf.map (homOfLE h).op y)
    have hres := tensorSection_restriction
      (HomologicalComplex.ιTensorObj K L (r : ℤ) (s : ℤ) ((r + s : ℕ) : ℤ)
        (by simp) ≫ t.f _) V W h x y
    simpa only [tensorChainSectionPair_apply, Hom.comp_app,
      ConcreteCategory.comp_apply, app_val_apply] using hres
  · intro r s V x y
    have hs := tensorChain_leibniz K L M t (r : ℤ) (s : ℤ) V x y
    change (M.d ((r + s : ℕ) : ℤ) ((r + s + 1 : ℕ) : ℤ)).val.app (op V)
      (tensorChainSectionPair K L M t r s V x y) =
      (eqToHom (congrArg (fun n : ℕ ↦ M.X (n : ℤ))
        (show r + 1 + s = r + s + 1 by omega))).val.app (op V)
        (tensorChainSectionPair K L M t (r + 1) s V
          ((K.d (r : ℤ) ((r + 1 : ℕ) : ℤ)).val.app (op V) x) y) +
      (-1 : ℤ) ^ r •
        (eqToHom (congrArg (fun n : ℕ ↦ M.X (n : ℤ))
          (show r + (s + 1) = r + s + 1 by omega))).val.app (op V)
          (tensorChainSectionPair K L M t r (s + 1) V x
            ((L.d (s : ℤ) ((s + 1 : ℕ) : ℤ)).val.app (op V) y))
    rw [tensorChainSectionPair_transport K L M t (r + 1) s (r + s + 1) (by omega),
      tensorChainSectionPair_transport K L M t r (s + 1) (r + s + 1) (by omega),
      tensorChainSectionPair_apply]
    simp only [app_val_apply, Units.smul_def, Int.coe_negOnePow_natCast] at hs
    exact hs
  · intro V x y
    change tensorChainSectionPair K L M t 0 0 V
      (((natAugmentation a).f 0).val.app (op V) x)
      (((natAugmentation b).f 0).val.app (op V) y) =
      ((natAugmentation c).f 0).val.app (op V) (tmulSection x y)
    simp only [natAugmentation, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
    rw [tensorChainSectionPair_apply]
    exact ht V x y


private theorem natAugmentation_naturality {X : Scheme.{v}} {F G : X.Modules}
    {K L : CochainComplex X.Modules ℤ}
    (a : (CochainComplex.singleFunctor X.Modules 0).obj F ⟶ K)
    (b : (CochainComplex.singleFunctor X.Modules 0).obj G ⟶ L)
    (φ : F ⟶ G) (l : K ⟶ L)
    (h : a ≫ l = (CochainComplex.singleFunctor X.Modules 0).map φ ≫ b) :
    natAugmentation a ≫ HomologicalComplex.restrictionMap l ComplexShape.embeddingUpNat =
      (CochainComplex.single₀ X.Modules).map φ ≫ natAugmentation b := by
  apply (CochainComplex.fromSingle₀Equiv _ F).injective
  apply Subtype.ext
  change (natAugmentation a).f 0 ≫ l.f 0 = φ ≫ (natAugmentation b).f 0
  simp only [natAugmentation, CochainComplex.fromSingle₀Equiv_symm_apply_f_zero]
  have h₀ := HomologicalComplex.congr_hom h 0
  simp only [HomologicalComplex.comp_f] at h₀
  change a.f 0 ≫ l.f 0 =
    ((HomologicalComplex.single X.Modules (ComplexShape.up ℤ) 0).map φ).f 0 ≫ b.f 0 at h₀
  rw [HomologicalComplex.single_map_f_self] at h₀
  dsimp [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq] at h₀
  erw [Category.comp_id, Category.id_comp] at h₀
  exact h₀

private theorem tensorChainSectionPair_naturality {X : Scheme.{v}}
    [MonoidalPreadditive X.Modules]
    {K L M K₁ L₁ M₁ : CochainComplex X.Modules ℤ}
    (u : HomologicalComplex.tensorObj K L ⟶ M)
    (u₁ : HomologicalComplex.tensorObj K₁ L₁ ⟶ M₁)
    (l : K ⟶ K₁) (r : L ⟶ L₁) (t : M ⟶ M₁)
    (h : u ≫ t = HomologicalComplex.tensorHom l r ≫ u₁)
    (p q : ℕ) (V : X.Opens)
    (a : Γ(K.X (p : ℤ), V)) (b : Γ(L.X (q : ℤ), V)) :
    (t.f ((p + q : ℕ) : ℤ)).val.app (op V)
      (tensorChainSectionPair K L M u p q V a b) =
    tensorChainSectionPair K₁ L₁ M₁ u₁ p q V
      ((l.f (p : ℤ)).val.app (op V) a) ((r.f (q : ℤ)).val.app (op V) b) := by
  have hh : HomologicalComplex.ιTensorObj K L (p : ℤ) (q : ℤ)
      ((p + q : ℕ) : ℤ) (by simp) ≫ u.f _ ≫ t.f _ =
      (l.f (p : ℤ) ⊗ₘ r.f (q : ℤ)) ≫
        HomologicalComplex.ιTensorObj K₁ L₁ (p : ℤ) (q : ℤ)
          ((p + q : ℕ) : ℤ) (by simp) ≫ u₁.f _ := by
    rw [← HomologicalComplex.comp_f, h, HomologicalComplex.comp_f]
    erw [HomologicalComplex.ι_mapBifunctorMap_assoc]
    simp [tensorHom_def, Category.assoc]
  have hs := congrArg (fun f ↦ f.app V (tmulSection a b)) hh
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, tensorHom_app_tmulSection] at hs
  simpa only [tensorChainSectionPair_apply, app_val_apply] using hs

/-- The usual injective comparison homotopy only requires exactness of the source. -/
private def resolutionHomotopyZero {X : Scheme.{v}} {F G : X.Modules}
    {K : CochainComplex X.Modules ℕ}
    (a : (CochainComplex.single₀ X.Modules).obj F ⟶ K) [QuasiIso a]
    (I : InjectiveResolution G) (f : K ⟶ I.cocomplex) (ha : a ≫ f = 0) :
    Homotopy f 0 := by
  let s₀ : K.X 1 ⟶ I.cocomplex.X 0 :=
    (CochainComplex.exact₀_of_quasiIso_single₀ a).descToInjective (f.f 0)
      (HomologicalComplex.congr_hom ha 0)
  have hs₀ : K.d 0 1 ≫ s₀ = f.f 0 :=
    (CochainComplex.exact₀_of_quasiIso_single₀ a).comp_descToInjective _ _
  let s₁ : K.X 2 ⟶ I.cocomplex.X 1 :=
    (CochainComplex.exact_succ_of_quasiIso_single₀ a 0).descToInjective
      (f.f 1 - s₀ ≫ I.cocomplex.d 0 1) (by
        rw [Preadditive.comp_sub, ← Category.assoc, hs₀, f.comm, sub_self])
  have hs₁ : K.d 1 2 ≫ s₁ = f.f 1 - s₀ ≫ I.cocomplex.d 0 1 :=
    (CochainComplex.exact_succ_of_quasiIso_single₀ a 0).comp_descToInjective _ _
  refine Homotopy.mkCoinductive _ s₀ (by simpa using hs₀.symm)
    s₁ (by simp [hs₁]) ?_
  intro n data
  rcases data with ⟨g, g', w⟩
  have hw : f.f (n + 1) = K.d (n + 1) (n + 2) ≫ g' +
      g ≫ I.cocomplex.d n (n + 1) := by simpa [add_comm] using w
  let s : K.X (n + 3) ⟶ I.cocomplex.X (n + 2) :=
    (CochainComplex.exact_succ_of_quasiIso_single₀ a (n + 1)).descToInjective
      (f.f (n + 2) - g' ≫ I.cocomplex.d _ _) (by
        rw [Preadditive.comp_sub, ← f.comm, hw, Preadditive.add_comp,
          Category.assoc, Category.assoc, HomologicalComplex.d_comp_d,
          comp_zero, add_zero, sub_self])
  have hs : K.d (n + 2) (n + 3) ≫ s =
      f.f (n + 2) - g' ≫ I.cocomplex.d _ _ :=
    (CochainComplex.exact_succ_of_quasiIso_single₀ a (n + 1)).comp_descToInjective _ _
  exact ⟨s, by simp [hs]⟩

/-- Two maps out of a resolution agreeing on the augmentation are homotopic. -/
private def resolutionHomotopy {X : Scheme.{v}} {F G : X.Modules}
    {K : CochainComplex X.Modules ℕ}
    (a : (CochainComplex.single₀ X.Modules).obj F ⟶ K) [QuasiIso a]
    (I : InjectiveResolution G) (f g : K ⟶ I.cocomplex) (h : a ≫ f = a ≫ g) :
    Homotopy f g :=
  Homotopy.equivSubZero.invFun
    (resolutionHomotopyZero a I (f - g) (by simp [Preadditive.comp_sub, h]))

/-- Transport a concrete cocycle through a cochain map. -/
private def map_cycle {R : Type v} [Ring R]
    {K L : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ L) (n : ℕ)
    (a : (K.sc n).moduleCatLeftHomologyData.K) :
    (L.sc n).moduleCatLeftHomologyData.K :=
  (L.sc n).moduleCatCyclesIso.hom
    (HomologicalComplex.cyclesMap φ n ((K.sc n).moduleCatCyclesIso.inv a))

private theorem map_cycle_val {R : Type v} [Ring R]
    {K L : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ L) (n : ℕ)
    (a : (K.sc n).moduleCatLeftHomologyData.K) :
    (map_cycle φ n a).val = φ.f n a.val := by
  have h : (K.sc n).moduleCatCyclesIso.inv ≫ HomologicalComplex.cyclesMap φ n ≫
      (L.sc n).moduleCatCyclesIso.hom ≫ (L.sc n).moduleCatLeftHomologyData.i =
      (K.sc n).moduleCatLeftHomologyData.i ≫ φ.f n := by
    rw [ShortComplex.moduleCatCyclesIso_hom_i]
    change (K.sc n).moduleCatCyclesIso.inv ≫
      ShortComplex.cyclesMap ((HomologicalComplex.shortComplexFunctor _ _ n).map φ) ≫
        (L.sc n).iCycles = _
    rw [ShortComplex.cyclesMap_i, ShortComplex.moduleCatCyclesIso_inv_iCycles_assoc]
    rfl
  exact congrArg (fun k ↦ k a) h

private theorem map_cycle_class {R : Type v} [Ring R]
    {K L : CochainComplex (ModuleCat.{v} R) ℕ} (φ : K ⟶ L) (n : ℕ)
    (a : (K.sc n).moduleCatLeftHomologyData.K) :
    HomologicalComplex.homologyMap φ n (cupCycleClass K n a) =
      cupCycleClass L n (map_cycle φ n a) := by
  have h : (K.sc n).moduleCatCyclesIso.inv ≫ (K.sc n).homologyπ ≫
      HomologicalComplex.homologyMap φ n =
      (K.sc n).moduleCatCyclesIso.inv ≫ HomologicalComplex.cyclesMap φ n ≫
        (L.sc n).homologyπ := by
    exact congrArg ((K.sc n).moduleCatCyclesIso.inv ≫ ·)
      (ShortComplex.homologyπ_naturality
        ((HomologicalComplex.shortComplexFunctor _ _ n).map φ))
  have h' : (K.sc n).moduleCatCyclesIso.inv ≫ (K.sc n).homologyπ ≫
      HomologicalComplex.homologyMap φ n =
      (K.sc n).moduleCatCyclesIso.inv ≫ HomologicalComplex.cyclesMap φ n ≫
        (L.sc n).moduleCatCyclesIso.hom ≫ (L.sc n).moduleCatCyclesIso.inv ≫
          (L.sc n).homologyπ := by
    rw [Iso.hom_inv_id_assoc]
    exact h
  exact congrArg (fun k ↦ k a) h'

/-- Computing classes are natural for any map over a coefficient morphism. -/
private theorem computingClass_naturality {X : Scheme.{v}} {F G : X.Modules}
    (D : CupAcyclicResolution F) (E : CupAcyclicResolution G) (φ : F ⟶ G)
    (l : D.K ⟶ E.K)
    (hl : D.augmentation ≫ l = (CochainComplex.single₀ X.Modules).map φ ≫
      E.augmentation) (n : ℕ)
    (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj D.K).sc n).moduleCatLeftHomologyData.K)
    (a' : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj E.K).sc n).moduleCatLeftHomologyData.K)
    (ha : a'.val = (l.f n).val.app (op ⊤) a.val) :
    E.class n a' = (RingedSpace.moduleCohomology X.toRingedSpace n).map φ (D.class n a) := by
  let : EnoughInjectives (SheafOfModules.{v} (moduleRings X.toRingedSpace)) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  let S := RingedSpace.globalSectionsFunctor X.toRingedSpace
  let T := S.mapHomologicalComplex (ComplexShape.up ℕ)
  have : QuasiIso D.augmentation := D.quasiIso
  let i := InjectiveResolution.desc φ E.I D.I
  have hi : D.I.ι ≫ i = (CochainComplex.single₀ X.Modules).map φ ≫ E.I.ι :=
    InjectiveResolution.desc_commutes φ E.I D.I
  have hcomp : D.augmentation ≫ (l ≫ E.comparison) =
      D.augmentation ≫ (D.comparison ≫ i) := by
    rw [← Category.assoc, hl, Category.assoc, E.over,
      ← Category.assoc D.augmentation, D.over, hi]
  let h := resolutionHomotopy D.augmentation E.I
    (l ≫ E.comparison) (D.comparison ≫ i) hcomp
  have hhom := (S.mapHomotopy h).homologyMap_eq n
  change HomologicalComplex.homologyMap (T.map (l ≫ E.comparison)) n =
    HomologicalComplex.homologyMap (T.map (D.comparison ≫ i)) n at hhom
  simp only [Functor.map_comp, HomologicalComplex.homologyMap_comp] at hhom
  have hin := InjectiveResolution.isoRightDerivedObj_inv_naturality φ D.I E.I i
    (InjectiveResolution.desc_commutes_zero φ E.I D.I) S n
  have heq : HomologicalComplex.homologyMap (T.map l) n ≫
      HomologicalComplex.homologyMap (T.map E.comparison) n ≫
        (E.I.isoRightDerivedObj S n).inv =
      HomologicalComplex.homologyMap (T.map D.comparison) n ≫
        (D.I.isoRightDerivedObj S n).inv ≫ (S.rightDerived n).map φ := by
    rw [← Category.assoc, hhom, Category.assoc]
    exact congrArg (HomologicalComplex.homologyMap (T.map D.comparison) n ≫ ·) hin.symm
  have hac : a' = map_cycle (T.map l) n a := by
    apply Subtype.ext
    exact ha.trans (map_cycle_val (T.map l) n a).symm
  subst a'
  change (E.I.isoRightDerivedObj S n).inv
      (HomologicalComplex.homologyMap (T.map E.comparison) n
        (cupCycleClass (T.obj E.K) n (map_cycle (T.map l) n a))) =
    (S.rightDerived n).map φ ((D.I.isoRightDerivedObj S n).inv
      (HomologicalComplex.homologyMap (T.map D.comparison) n
        (cupCycleClass (T.obj D.K) n a)))
  rw [← map_cycle_class (T.map l) n a]
  exact congrArg (fun f ↦ f (cupCycleClass (T.obj D.K) n a)) heq

/-- Coefficient maps lift simultaneously to computing resolution pairings.
The three lifted maps commute with the section pairing in every bidegree and
induce the coefficient maps under the resolution class identifications. This is
resolution-level data; no cup product on cohomology is assumed.
Source: Stacks Project, Sections 20.30 and 20.31, Tags 0FKR and 0FKU.
(blueprint: lem-sc-module-cup-coefficient-resolution-maps)
Proof: use the functorial cosimplicial Godement resolution for the six sheaves
F, G, F1, G1, F tensor G, and F1 tensor G1. Apply its functorial action to phi,
psi and phi tensor psi. The natural stalkwise tensor pairing commutes with
these maps. In the Alexander--Whitney formula the same front/back face maps
are used on both sides; their naturality proves the pairing equation in every
bidegree and on every open set. Restrict the resulting complexes to natural
indices and equip them with injective comparisons as in the computing-flasque
resolution construction. Each comparison induces an isomorphism on global
homology because its terms are flasque. A lifted coefficient map and an
injective-resolution lift agree over the degree-zero augmentation. The
comparison theorem makes their composites into the target injective complex
homotopic; applying global sections and homology makes them equal.
InjectiveResolution.isoRightDerivedObj_inv_naturality then gives the class
map equation for every degree and every pair of cycles with the stated
underlying-section equality. This proves all three class equations. No
quasi-coherence or flatness is used. For zero maps, zero sheaves, and the empty
scheme the same additive functor and tensor pairing apply. -/
theorem moduleCup_coefficient_resolution_maps (X : Scheme.{v})
    (F G F₁ G₁ : X.Modules) (φ : F ⟶ F₁) (ψ : G ⟶ G₁) :
    ∃ (D : CupResolutionPairing F G) (E : CupResolutionPairing F₁ G₁)
      (l : D.left.K ⟶ E.left.K) (r : D.right.K ⟶ E.right.K)
      (t : D.target.K ⟶ E.target.K),
      (∀ (n : ℕ)
        (a : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.left.K).sc n).moduleCatLeftHomologyData.K)
        (a' : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj E.left.K).sc n).moduleCatLeftHomologyData.K),
        a'.val = (l.f n).val.app (op ⊤) a.val →
          E.left.class n a' =
            (RingedSpace.moduleCohomology X.toRingedSpace n).map φ (D.left.class n a)) ∧
      (∀ (n : ℕ)
        (b : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.right.K).sc n).moduleCatLeftHomologyData.K)
        (b' : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj E.right.K).sc n).moduleCatLeftHomologyData.K),
        b'.val = (r.f n).val.app (op ⊤) b.val →
          E.right.class n b' =
            (RingedSpace.moduleCohomology X.toRingedSpace n).map ψ (D.right.class n b)) ∧
      (∀ (n : ℕ)
        (c : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj D.target.K).sc n).moduleCatLeftHomologyData.K)
        (c' : ((((RingedSpace.globalSectionsFunctor X.toRingedSpace).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj E.target.K).sc n).moduleCatLeftHomologyData.K),
        c'.val = (t.f n).val.app (op ⊤) c.val →
          E.target.class n c' =
            (RingedSpace.moduleCohomology X.toRingedSpace n).map
              (@id (F ⊗ G ⟶ F₁ ⊗ G₁) (φ ⊗ₘ ψ)) (D.target.class n c)) ∧
      (∀ (p q : ℕ) (V : X.Opens)
        (a : Γ(D.left.K.X p, V)) (b : Γ(D.right.K.X q, V)),
        (t.f (p + q)).val.app (op V) (D.pair p q V a b) =
          E.pair p q V ((l.f p).val.app (op V) a) ((r.f q).val.app (op V) b)) := by
  let : MonoidalPreadditive X.Modules :=
    Classical.choice (SheafOfModules.tensorClosed X.sheaf).1
  obtain ⟨K, L, M, a, b, c, ha, hb, hc, hK, hL, hM, fK, fL, fM, u, hu, hrest⟩ :=
    moduleCup_godement_coefficient_complexes X F G F₁ G₁ φ ψ
  obtain ⟨K₁, L₁, M₁, a₁, b₁, c₁, ha₁, hb₁, hc₁, hK₁, hL₁, hM₁, fK₁, fL₁, fM₁,
    u₁, hu₁, l, r, t, hl, hr, ht, hpair⟩ := hrest
  let D := computingPairing K L M a b c ha hb hc hK hL hM fK fL fM u hu
  let E := computingPairing K₁ L₁ M₁ a₁ b₁ c₁ ha₁ hb₁ hc₁ hK₁ hL₁ hM₁
    fK₁ fL₁ fM₁ u₁ hu₁
  let l' : D.left.K ⟶ E.left.K :=
    HomologicalComplex.restrictionMap l ComplexShape.embeddingUpNat
  let r' : D.right.K ⟶ E.right.K :=
    HomologicalComplex.restrictionMap r ComplexShape.embeddingUpNat
  let t' : D.target.K ⟶ E.target.K :=
    HomologicalComplex.restrictionMap t ComplexShape.embeddingUpNat
  refine ⟨D, E, l', r', t', ?_, ?_, ?_, ?_⟩
  · intro n z z' hz
    apply computingClass_naturality D.left E.left φ l' _ n z z' hz
    change natAugmentation a ≫ HomologicalComplex.restrictionMap l
      ComplexShape.embeddingUpNat = _
    exact natAugmentation_naturality a a₁ φ l hl
  · intro n z z' hz
    apply computingClass_naturality D.right E.right ψ r' _ n z z' hz
    change natAugmentation b ≫ HomologicalComplex.restrictionMap r
      ComplexShape.embeddingUpNat = _
    exact natAugmentation_naturality b b₁ ψ r hr
  · intro n z z' hz
    apply computingClass_naturality D.target E.target (φ ⊗ₘ ψ) t' _ n z z' hz
    change natAugmentation c ≫ HomologicalComplex.restrictionMap t
      ComplexShape.embeddingUpNat = _
    exact natAugmentation_naturality c c₁ (φ ⊗ₘ ψ) t ht
  · intro p q V x y
    exact tensorChainSectionPair_naturality u u₁ l r t hpair p q V x y

end
end AlgebraicGeometry.Scheme.Modules
