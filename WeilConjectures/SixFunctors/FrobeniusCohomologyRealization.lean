/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.FiniteFieldDatum.FrobeniusDetailed
public import WeilConjectures.SixFunctors.FrobeniusCohomologyTransport
public import WeilConjectures.CategoryTheory.DerivedCategory.Field.FieldDerivedScalarTower
public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.SmoothPurity.Sf.SfCommonStageDirectImage
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.SixFunctors.CommonStageCompactWeilCohomology
public import WeilConjectures.Compactification.RefinementCategory
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # Canonical cohomology realizations before common-stage descent

Source: Deligne, Weil II (1.1.10)--(1.1.14)
(blueprint: lem-weil-frobenius-cohomology-transport-iso).

The scalar tower, rational cohomology functors, and actual stage comparisons are
kept here so their coefficient coherence can be proved independently of descent.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

open scoped TensorProduct ChangeOfRings

namespace WeilConjectures

open FrobeniusExchange

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard

section CoefficientRealization

/-- The coefficient embedding between the two canonical common-size lifts.
Source: Deligne, Weil II (1.1.10), coefficient realization
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCoefficientLiftHom {F : Type u} [Field F] {Ω : Type v} [Field Ω]
    (φ : F →+* Ω) : ULift.{v, u} F →+* ULift.{u, v} Ω :=
  (ULift.ringEquiv : ULift.{u, v} Ω ≃+* Ω).symm.toRingHom.comp
    (φ.comp (ULift.ringEquiv : ULift.{v, u} F ≃+* F).toRingHom)

/-- The ordinary exact scalar-and-size transport underlying the recorded derived functor.
Source: Deligne, Weil II (1.1.10), coefficient realization
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCoefficientModules {F : Type u} [Field F] {Ω : Type v} [Field Ω]
    (φ : F →+* Ω) : ModuleCat.{u} F ⥤ ModuleCat.{max u v} Ω :=
  let ψ := frobeniusCoefficientLiftHom φ
  ModuleCat.uliftFunctor.{v, u} F ⋙
    ModuleCat.restrictScalars.{max u v, max u v, u}
      (ULift.ringEquiv : ULift.{v, u} F ≃+* F).toRingHom ⋙
    ModuleCat.extendScalars.{max u v, max u v, max u v} ψ ⋙
    ModuleCat.restrictScalars.{max u v, v, max u v}
      (ULift.ringEquiv : ULift.{u, v} Ω ≃+* Ω).symm.toRingHom

private def coefficientTowerEquiv
    {F G : Type u} [Field F] [Field G] {Ω : Type v} [Field Ω]
    (φ : F →+* G) (ψ : G →+* Ω) (M : ModuleCat.{u} F) :
    ((ModuleCat.extendScalars φ ⋙ frobeniusCoefficientModules ψ).obj M) ≃ₗ[Ω]
      (frobeniusCoefficientModules (ψ.comp φ)).obj M := by
  letI := φ.toAlgebra
  letI := ψ.toAlgebra
  letI := (ψ.comp φ).toAlgebra
  letI : IsScalarTower F G Ω := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra (ULift.{v, u} F) (ULift.{v, u} G) :=
    ((ULift.ringEquiv : ULift.{v, u} G ≃+* G).symm.toRingHom.comp
      (φ.comp (ULift.ringEquiv : ULift.{v, u} F ≃+* F).toRingHom)).toAlgebra
  letI : Algebra (ULift.{v, u} G) (ULift.{u, v} Ω) :=
    (frobeniusCoefficientLiftHom ψ).toAlgebra
  letI : Algebra (ULift.{v, u} F) (ULift.{u, v} Ω) :=
    (frobeniusCoefficientLiftHom (ψ.comp φ)).toAlgebra
  letI : IsScalarTower (ULift.{v, u} F) (ULift.{v, u} G) (ULift.{u, v} Ω) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let e : ULift.{v, u} ((ModuleCat.extendScalars φ).obj M) ≃ₗ[ULift.{v, u} G]
      ULift.{v, u} G ⊗[ULift.{v, u} F] ULift.{v, u} M :=
    { __ := TensorProduct.AlgebraTensorModule.uliftEquiv F G G M
      map_smul' := fun a x ↦
        (TensorProduct.AlgebraTensorModule.uliftEquiv F G G M).map_smul a.down x }
  let e' := TensorProduct.AlgebraTensorModule.congr
      (LinearEquiv.refl (ULift.{u, v} Ω) (ULift.{u, v} Ω)) e ≪≫ₗ
    TensorProduct.AlgebraTensorModule.cancelBaseChange
      (ULift.{v, u} F) (ULift.{v, u} G) (ULift.{u, v} Ω)
      (ULift.{u, v} Ω) (ULift.{v, u} M)
  exact
    { __ := e'
      map_smul' := fun a x ↦ e'.map_smul (ULift.up a) x }

private theorem coefficientTowerEquiv_tmul
    {F G : Type u} [Field F] [Field G] {Ω : Type v} [Field Ω]
    (φ : F →+* G) (ψ : G →+* Ω) (M : ModuleCat.{u} F)
    (a : ULift.{u, v} Ω) (b : G) (m : M) :
    coefficientTowerEquiv φ ψ M
        (a ⊗ₜ[ULift.{v, u} G, frobeniusCoefficientLiftHom ψ]
          ULift.up (b ⊗ₜ[F, φ] m)) =
      (a * ULift.up (ψ b)) ⊗ₜ[ULift.{v, u} F,
        frobeniusCoefficientLiftHom (ψ.comp φ)] ULift.up m := by
  change (ULift.up (ψ b) * a) ⊗ₜ[ULift.{v, u} F,
    frobeniusCoefficientLiftHom (ψ.comp φ)] ULift.up m = _
  rw [mul_comm]

attribute [local irreducible] coefficientTowerEquiv

private theorem coefficientTowerEquiv_natural
    {F G : Type u} [Field F] [Field G] {Ω : Type v} [Field Ω]
    (φ : F →+* G) (ψ : G →+* Ω) {M N : ModuleCat.{u} F} (f : M ⟶ N) :
    (ModuleCat.extendScalars φ ⋙ frobeniusCoefficientModules ψ).map f ≫
        (coefficientTowerEquiv φ ψ N).toModuleIso.hom =
      (coefficientTowerEquiv φ ψ M).toModuleIso.hom ≫
        (frobeniusCoefficientModules (ψ.comp φ)).map f := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul a x =>
    obtain ⟨x⟩ := x
    induction x using TensorProduct.induction_on with
    | zero =>
      rw [show (ULift.up (0 : (ModuleCat.extendScalars φ).obj M) :
        ULift.{v, u} _) = 0 from rfl, TensorProduct.tmul_zero]
      simp
    | add x y hx hy =>
      rw [show (ULift.up (x + y) : ULift.{v, u} ((ModuleCat.extendScalars φ).obj M)) =
        ULift.up x + ULift.up y from rfl, TensorProduct.tmul_add]
      simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul b m =>
      change coefficientTowerEquiv φ ψ N
          (a ⊗ₜ[ULift.{v, u} G, frobeniusCoefficientLiftHom ψ]
            ULift.up (b ⊗ₜ[F, φ] f m)) =
        (frobeniusCoefficientModules (ψ.comp φ)).map f
          (coefficientTowerEquiv φ ψ M
            (a ⊗ₜ[ULift.{v, u} G, frobeniusCoefficientLiftHom ψ]
              ULift.up (b ⊗ₜ[F, φ] m)))
      rw [coefficientTowerEquiv_tmul, coefficientTowerEquiv_tmul]
      rfl

/-- Balanced tensor multiplication uniquely fixes the size-compatible tower comparison.
Source: Deligne, Weil II (1.1.10), coefficient extension
(blueprint: lem-weil-frobenius-cohomology-transport-iso).
Proof: send a tensor up(b tensor m) to (a * up(ψ b)) tensor up(m).
Balancing over both fields proves well-definedness. The inverse sends a tensor
up(m) to a tensor up(1 tensor m); the tensor relations prove both inverse laws.
Pure tensors generate, proving naturality and uniqueness. -/
theorem frobeniusCoefficientModulesTower_existsUnique
    {F G : Type u} [Field F] [Field G] {Ω : Type v} [Field Ω]
    (φ : F →+* G) (ψ : G →+* Ω) :
    ∃! e : ModuleCat.extendScalars.{u, u, u} φ ⋙ frobeniusCoefficientModules ψ ≅
        frobeniusCoefficientModules (ψ.comp φ),
      ∀ (M : ModuleCat.{u} F) (a : ULift.{u, v} Ω) (b : G) (m : M),
        e.hom.app M
          (a ⊗ₜ[ULift.{v, u} G, frobeniusCoefficientLiftHom ψ]
            ULift.up (b ⊗ₜ[F, φ] m)) =
          (a * ULift.up (ψ b)) ⊗ₜ[ULift.{v, u} F, frobeniusCoefficientLiftHom (ψ.comp φ)]
            ULift.up m := by
  let e : ModuleCat.extendScalars φ ⋙ frobeniusCoefficientModules ψ ≅
      frobeniusCoefficientModules (ψ.comp φ) :=
    NatIso.ofComponents (fun M ↦ (coefficientTowerEquiv φ ψ M).toModuleIso)
      (fun f ↦ coefficientTowerEquiv_natural φ ψ f)
  refine ⟨e, ?_, ?_⟩
  · intro M a b m
    exact coefficientTowerEquiv_tmul φ ψ M a b m
  · intro e' he'
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul a x =>
      obtain ⟨x⟩ := x
      induction x using TensorProduct.induction_on with
      | zero =>
        rw [show (ULift.up (0 : (ModuleCat.extendScalars φ).obj M) :
          ULift.{v, u} _) = 0 from rfl, TensorProduct.tmul_zero]
        simp
      | add x y hx hy =>
        rw [show (ULift.up (x + y) : ULift.{v, u} ((ModuleCat.extendScalars φ).obj M)) =
          ULift.up x + ULift.up y from rfl, TensorProduct.tmul_add]
        simpa only [map_add] using congrArg₂ (· + ·) hx hy
      | tmul b m => exact (he' M a b m).trans (coefficientTowerEquiv_tmul φ ψ M a b m).symm

/-- The derived tower comparison is the image of the specified balanced tensor map.
Source: Deligne, Weil II (1.1.10), common-stage realization
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCoefficientTower {F G : Type u} [Field F] [Field G]
    {Ω : Type v} [Field Ω] (φ : F →+* G) (ψ : G →+* Ω) :
    DerivedCategory.fieldDerivedScalarExtension φ ⋙
        frobeniusCohomologyCoefficientExtension ψ ≅
      frobeniusCohomologyCoefficientExtension (ψ.comp φ) := by
  letI : HasDerivedCategory.{u} (ModuleCat.{u} F) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  letI : HasDerivedCategory.{u} (ModuleCat.{u} G) :=
    HasDerivedCategory.ofIsGrothendieckAbelian _
  letI : HasDerivedCategory.{(max u v) + 1} (ModuleCat.{max u v} Ω) :=
    HasDerivedCategory.standard _
  let A := frobeniusCoefficientModules ψ
  let B := frobeniusCoefficientModules (ψ.comp φ)
  letI : A.Additive := by
    dsimp [A, frobeniusCoefficientModules, frobeniusCoefficientLiftHom]
    infer_instance
  letI : PreservesFiniteLimits A := by
    dsimp [A, frobeniusCoefficientModules, frobeniusCoefficientLiftHom]
    infer_instance
  letI : PreservesFiniteColimits A := by
    dsimp [A, frobeniusCoefficientModules, frobeniusCoefficientLiftHom]
    infer_instance
  letI : B.Additive := by
    dsimp [B, frobeniusCoefficientModules, frobeniusCoefficientLiftHom]
    infer_instance
  letI : PreservesFiniteLimits B := by
    dsimp [B, frobeniusCoefficientModules, frobeniusCoefficientLiftHom]
    infer_instance
  letI : PreservesFiniteColimits B := by
    dsimp [B, frobeniusCoefficientModules, frobeniusCoefficientLiftHom]
    infer_instance
  exact (Functor.mapDerivedCategoryCompIso _ A).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (frobeniusCoefficientModulesTower_existsUnique φ ψ).exists.choose

end CoefficientRealization

section RationalScalarProof
universe r s w x a
open TensorProduct

private theorem localizedIso
    {R : Type r} [CommRing R] {S : Type s} [CommRing S]
    {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
    {D : Type w} [Category.{x} D] [Preadditive D] [Linear S D]
    (p : R) (q : S) (φ : Localization.Away p →+* Localization.Away q)
    (F G : C ⥤ D)
    (Fq Gq : ScalarLocalization R C p ⥤ ScalarLocalization S D q)
    [Fq.Additive] [Gq.Additive]
    (hF : ∀ K, Fq.obj K = ⟨F.obj K.obj⟩)
    (hG : ∀ K, Gq.obj K = ⟨G.obj K.obj⟩)
    (mF : ∀ (K L : C) (f : K ⟶ L) (a : Localization.Away p),
      HEq (Fq.map (a ⊗ₜ[R] f : ScalarLocalization.mk K ⟶ ScalarLocalization.mk L))
        (φ a ⊗ₜ[S] F.map f))
    (mG : ∀ (K L : C) (f : K ⟶ L) (a : Localization.Away p),
      HEq (Gq.map (a ⊗ₜ[R] f : ScalarLocalization.mk K ⟶ ScalarLocalization.mk L))
        (φ a ⊗ₜ[S] G.map f))
    (e : F ≅ G) :
    ∃! eq : Fq ≅ Gq, ∀ K,
      HEq (eq.hom.app K) ((ScalarLocalization.localization S D q).map (e.hom.app K.obj)) := by
  let Q := ScalarLocalization.localization S D q
  let app (K : ScalarLocalization R C p) : Fq.obj K ≅ Gq.obj K :=
    eqToIso (hF K) ≪≫ Q.mapIso (e.app K.obj) ≪≫ (eqToIso (hG K)).symm
  have happ (K) : (app K).hom =
      eqToHom (hF K) ≫ Q.map (e.hom.app K.obj) ≫ eqToHom (hG K).symm := rfl
  have hn {K L : ScalarLocalization R C p} (f : K ⟶ L) :
      Fq.map f ≫ (app L).hom = (app K).hom ≫ Gq.map f := by
    induction f using TensorProduct.induction_on with
    | zero => simp
    | tmul a f =>
      have hf := (conj_eqToHom_iff_heq _ _ (hF K) (hF L)).2 (mF K.obj L.obj f a)
      have hg := (conj_eqToHom_iff_heq _ _ (hG K) (hG L)).2 (mG K.obj L.obj f a)
      have hh : (φ a ⊗ₜ[S] F.map f :
          ScalarLocalization.mk (F.obj K.obj) ⟶ ScalarLocalization.mk (F.obj L.obj)) ≫
          Q.map (e.hom.app L.obj) = Q.map (e.hom.app K.obj) ≫
            (φ a ⊗ₜ[S] G.map f) := by
        change ScalarLocalization.composition S D q _ _ _ (1 ⊗ₜ[S] e.hom.app L.obj)
            (φ a ⊗ₜ[S] F.map f) =
          ScalarLocalization.composition S D q _ _ _ (φ a ⊗ₜ[S] G.map f)
            (1 ⊗ₜ[S] e.hom.app K.obj)
        simp only [ScalarLocalization.composition_tmul, one_mul, mul_one,
          e.hom.naturality]
      rw [happ, happ, hf, hg]
      simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
        Category.id_comp] using
        congrArg (fun z ↦ eqToHom (hF K) ≫ z ≫ eqToHom (hG L).symm) hh
    | add f g hf hg =>
      rw [Fq.map_add, Gq.map_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
  refine ⟨NatIso.ofComponents app hn, ?_, ?_⟩
  · intro K
    exact (conj_eqToHom_iff_heq _ _ (hF K) (hG K)).1 (happ K)
  · intro eq heq
    apply Iso.ext
    apply NatTrans.ext
    funext K
    exact eq_of_heq ((heq K).trans
      ((conj_eqToHom_iff_heq _ _ (hF K) (hG K)).1 (happ K)).symm)

private theorem rationalModelObj
    (l : ℕ) [Fact l.Prime] (k : Type a) [Field k] (hl : IsUnit (l : k))
    {X Y : Scheme.{a}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [_ix : ∀ x : X, Invertible (l : X.residueField x)]
    [_iy : ∀ y : Y, Invertible (l : Y.residueField y)]
    (gX : X ⟶ X) (gY : Y ⟶ Y) [IsIso gX] [IsIso gY]
    (M : SupportModel f gX gY) (E : Type a) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] :
    ∀ K, (modelRationalFunctor l k hl f gX gY M E).obj K =
      ⟨(modelFunctor l k hl f gX gY M E).obj K.obj⟩ := by
  delta modelFunctor
  cases M <;> intro K <;> rfl

private theorem rationalModelMap
    (l : ℕ) [Fact l.Prime] (k : Type a) [Field k] (hl : IsUnit (l : k))
    {X Y : Scheme.{a}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [_ix : ∀ x : X, Invertible (l : X.residueField x)]
    [_iy : ∀ y : Y, Invertible (l : Y.residueField y)]
    (gX : X ⟶ X) (gY : Y ⟶ Y) [IsIso gX] [IsIso gY]
    (M : SupportModel f gX gY) (E : Type a) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E]
    (K N : sfIntegralConstructibleCategory l E X) (b : K ⟶ N)
    (a : Localization.Away (Padic.coefficientExtensionUniformizer l E)) :
    HEq ((modelRationalFunctor l k hl f gX gY M E).map
      (a ⊗ₜ[Padic.coefficientExtensionIntegers l E] b :
        (sfRationalConstructibleLocalization l E X).obj K ⟶
          (sfRationalConstructibleLocalization l E X).obj N))
      (a ⊗ₜ[Padic.coefficientExtensionIntegers l E]
        (modelFunctor l k hl f gX gY M E).map b) := by
  delta modelFunctor
  cases M <;> apply heq_of_eq <;> exact LinearMap.baseChange_tmul _ _ _

private theorem mapHEq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {K N K' N' : C} {f : K ⟶ N} {g : K' ⟶ N'}
    (hK : K = K') (hN : N = N') (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hK
  cases hN
  cases h
  rfl

private theorem rationalModelScalar
    (l : ℕ) [Fact l.Prime] (k : Type a) [Field k] (hl : IsUnit (l : k))
    {X Y : Scheme.{a}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [ix : ∀ x : X, Invertible (l : X.residueField x)]
    [iy : ∀ y : Y, Invertible (l : Y.residueField y)]
    (gX : X ⟶ X) (gY : Y ⟶ Y) [IsIso gX] [IsIso gY]
    (M : SupportModel f gX gY) (E L : Type a) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] (ι : E →ₐ[ℚ_[l]] L) :
    ∃! b : modelRationalFunctor l k hl f gX gY M E ⋙
        sfRationalScalarExtension l E Y 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ≅
      sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ⋙
        modelRationalFunctor l k hl f gX gY M L,
      ∀ K : sfRationalConstructibleCategory l E X,
        HEq (b.hom.app K) ((sfRationalConstructibleLocalization l L Y).map
          ((modelScalar (ix := ix) (iy := iy) l k hl f gX gY M E L ι).hom.app K.obj)) := by
  let T := modelFunctor l k hl f gX gY M E
  let U := modelFunctor l k hl f gX gY M L
  let Tq := modelRationalFunctor l k hl f gX gY M E
  let Uq := modelRationalFunctor l k hl f gX gY M L
  let SX := scalar l E L ι X
  let SY := scalar l E L ι Y
  let SXq := sfRationalScalarExtension l E X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι
  let SYq := sfRationalScalarExtension l E Y 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι
  let φ : Localization.Away (Padic.coefficientExtensionUniformizer l E) →+*
      Localization.Away (Padic.coefficientExtensionUniformizer l L) :=
    (sfRationalCoefficientEquiv l L).symm.toRingHom.comp
      (ι.toRingHom.comp (sfRationalCoefficientEquiv l E).toRingHom)
  have hSX := (sfRationalScalarExtension_existsUnique l E X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec
  have hSY := (sfRationalScalarExtension_existsUnique l E Y 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).exists.choose_spec
  have hT := rationalModelObj l k hl f gX gY M E
  have hU := rationalModelObj l k hl f gX gY M L
  have ht : Tq.Additive := by
    cases M <;> exact ⟨fun {K N b c} ↦ LinearMap.map_add _ b c⟩
  have hu : Uq.Additive := by
    cases M <;> exact ⟨fun {K N b c} ↦ LinearMap.map_add _ b c⟩
  have hF (K : sfRationalConstructibleCategory l E X) :
      (Tq ⋙ SYq).obj K = ⟨(T ⋙ SY).obj K.obj⟩ := by
    exact (congrArg SYq.obj (hT K)).trans (hSY.2.1 ⟨T.obj K.obj⟩)
  have hG (K : sfRationalConstructibleCategory l E X) :
      (SXq ⋙ Uq).obj K = ⟨(SX ⋙ U).obj K.obj⟩ := by
    exact (congrArg Uq.obj (hSX.2.1 K)).trans (hU ⟨SX.obj K.obj⟩)
  apply localizedIso _ _ φ (T ⋙ SY) (SX ⋙ U) (Tq ⋙ SYq) (SXq ⋙ Uq) hF hG
    ?_ ?_ (modelScalar (ix := ix) (iy := iy) l k hl f gX gY M E L ι)
  · intro K N b c
    exact (mapHEq SYq (hT ⟨K⟩) (hT ⟨N⟩)
      (rationalModelMap l k hl f gX gY M E K N b c)).trans
        (hSY.2.2 (T.obj K) (T.obj N) (T.map b) c)
  · intro K N b c
    exact (mapHEq Uq (hSX.2.1 ⟨K⟩) (hSX.2.1 ⟨N⟩)
      (hSX.2.2 K N b c)).trans
        (rationalModelMap l k hl f gX gY M L (SX.obj K) (SX.obj N)
          (SX.map b) (φ c))

end RationalScalarProof

section GeometricFunctors
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]

/-- The actual rational RΓ or RΓ_c functor used by the transport component.
Source: Deligne, Weil II (1.1.14); the retained coefficient-stage recipe
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyRationalFunctor (c₀ : Compactification Y₀.hom) (compact : Bool) :=
  letI := sfWeilPrimeInvertible D l hl Y₀
  letI := frobeniusPointPrimeInvertible D l hl
  letI : IsIso (galois D Y₀) := inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (D.geometricFiber Y₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber Y₀).hom⟩
  letI : (D.geometricFiber Y₀).hom.IsOver (Spec (.of D.k)) := ⟨Category.comp_id _⟩
  letI : IsSeparated (D.geometricFiber Y₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  modelRationalFunctor l D.k (zlClosurePrimeUnit D l hl)
    (D.geometricFiber Y₀).hom (galois D Y₀) (frobeniusPointIso D).hom
    (if compact then frobeniusCohomologyCompactModel D Y₀ c₀
      else frobeniusCohomologyDirectModel D Y₀) E ⋙ pointRationalFibre D l hl E



/-- The actual localized operation, before the point fibre is applied.
Source: Deligne, Weil II (1.1.14), ordinary and compact recipes
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyRationalOperation (c₀ : Compactification Y₀.hom) (compact : Bool) :=
  letI := sfWeilPrimeInvertible D l hl Y₀
  letI := frobeniusPointPrimeInvertible D l hl
  letI : IsIso (galois D Y₀) := inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (D.geometricFiber Y₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber Y₀).hom⟩
  letI : (D.geometricFiber Y₀).hom.IsOver (Spec (.of D.k)) := ⟨Category.comp_id _⟩
  letI : IsSeparated (D.geometricFiber Y₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  modelRationalFunctor l D.k (zlClosurePrimeUnit D l hl)
    (D.geometricFiber Y₀).hom (galois D Y₀) (frobeniusPointIso D).hom
    (if compact then frobeniusCohomologyCompactModel D Y₀ c₀
      else frobeniusCohomologyDirectModel D Y₀) E

/-- The integral coefficient mate retained by the ordinary or compact recipe.
Source: Deligne, Weil II (1.1.14), coefficient descent
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyIntegralScalar (c₀ : Compactification Y₀.hom) (compact : Bool)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) :=
  letI := sfWeilPrimeInvertible D l hl Y₀
  letI := frobeniusPointPrimeInvertible D l hl
  letI : IsIso (galois D Y₀) := inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)
  letI : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  letI : (D.geometricFiber Y₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber Y₀).hom⟩
  letI : (D.geometricFiber Y₀).hom.IsOver (Spec (.of D.k)) := ⟨Category.comp_id _⟩
  letI : IsSeparated (D.geometricFiber Y₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  letI : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  letI : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  modelScalar l D.k (zlClosurePrimeUnit D l hl)
    (D.geometricFiber Y₀).hom (galois D Y₀) (frobeniusPointIso D).hom
    (if compact then frobeniusCohomologyCompactModel D Y₀ c₀
      else frobeniusCohomologyDirectModel D Y₀) E L ι

/-- Rational operation comparison, uniquely normalized by the integral coefficient mate.
Source: Deligne, Weil II (1.1.14), coefficient descent
(blueprint: lem-weil-frobenius-cohomology-transport-iso).
Proof: localize the displayed integral comparison and its inverse. The scalar
linearity of its components makes the localized maps natural on every rational
Hom. The raw localization has the same integral object representatives, so the
component equation fixes every component and proves uniqueness. -/
theorem frobeniusCohomologyRationalOperationScalar_existsUnique
    (c₀ : Compactification Y₀.hom) (compact : Bool)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) :
    ∃! b : frobeniusCohomologyRationalOperation D l hl E Y₀ c₀ compact ⋙
        sfRationalScalarExtension l E (Spec (.of D.k)) 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ≅
      sfRationalScalarExtension l E (D.geometricFiber Y₀).left 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ⋙
        frobeniusCohomologyRationalOperation D l hl L Y₀ c₀ compact,
      ∀ K : sfRationalConstructibleCategory l E (D.geometricFiber Y₀).left,
        HEq (b.hom.app K)
          ((sfRationalConstructibleLocalization l L (Spec (.of D.k))).map
            ((frobeniusCohomologyIntegralScalar D l hl E Y₀ c₀ compact L ι).hom.app K.obj)) := by
  let := sfWeilPrimeInvertible D l hl Y₀
  let := frobeniusPointPrimeInvertible D l hl
  let : IsIso (galois D Y₀) := inferInstanceAs (IsIso (D.geometricFrobenius Y₀).hom)
  let : (Spec (.of D.k)).Over (Spec (.of D.k)) := ⟨𝟙 _⟩
  let : (D.geometricFiber Y₀).left.Over (Spec (.of D.k)) :=
    ⟨(D.geometricFiber Y₀).hom⟩
  let : (D.geometricFiber Y₀).hom.IsOver (Spec (.of D.k)) := ⟨Category.comp_id _⟩
  let : IsSeparated (D.geometricFiber Y₀).hom :=
    inferInstanceAs (IsSeparated (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))))
  let : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).1
  let : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) :=
    (fiber_finiteType D Y₀).2
  exact rationalModelScalar l D.k (zlClosurePrimeUnit D l hl)
    (D.geometricFiber Y₀).hom (galois D Y₀) (frobeniusPointIso D).hom
    (if compact then frobeniusCohomologyCompactModel D Y₀ c₀
      else frobeniusCohomologyDirectModel D Y₀) E L ι

/-- The normalized rational operation scalar comparison.
Source: Deligne, Weil II (1.1.14), coefficient descent
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyRationalOperationScalar
    (c₀ : Compactification Y₀.hom) (compact : Bool)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) :=
  (frobeniusCohomologyRationalOperationScalar_existsUnique D l hl E Y₀ c₀ compact L ι).exists.choose

/-- Cohomology scalar comparison: the localized operation mate followed by the
recorded point-fibre scalar comparison, with their actual associators.
Source: Deligne, Weil II (1.1.14), coefficient descent
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyRationalScalar
    (c₀ : Compactification Y₀.hom) (compact : Bool)
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) :
    frobeniusCohomologyRationalFunctor D l hl E Y₀ c₀ compact ⋙
        DerivedCategory.pointFdScalarExtension ι.toRingHom ≅
      sfRationalScalarExtension l E (D.geometricFiber Y₀).left 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι ⋙
        frobeniusCohomologyRationalFunctor D l hl L Y₀ c₀ compact :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (frobeniusCohomologyRationalOperation D l hl E Y₀ c₀ compact)
      (pointRationalFibreScalarIso D l hl E L ι).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (frobeniusCohomologyRationalOperationScalar D l hl E Y₀ c₀ compact L ι)
      (pointRationalFibre D l hl L) ≪≫ Functor.associator _ _ _

end GeometricFunctors

section CommonStageFunctors
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion)
open GeneralAlgebraicallyClosedCoefficients (stageSystem)
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (Y₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
  [IsSeparated Y₀.hom]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The canonical embedding of the actual small coefficient model into Ω.
Source: Deligne, Weil II (1.1.10), finite fields of definition
(blueprint: lem-weil-frobenius-cohomology-transport-iso). -/
def frobeniusCohomologyStageEmbedding (E : Index l Ω) : Coefficient.{u} l Ω E →+* Ω :=
  E.val.subtype.comp (Shrink.algEquiv ℚ_[l] E.val).toRingHom

set_option linter.unusedSectionVars false in
end CommonStageFunctors

end WeilConjectures
