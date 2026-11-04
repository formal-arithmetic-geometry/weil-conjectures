/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassChern
public import WeilConjectures.SixFunctors.SequenceModuleEvaluation.SequenceModulePullbackEvaluation
public import WeilConjectures.CategoryTheory.Constant.ConstantFiniteFreeExtensionLeftExact
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.Data.ZMod.QuotientRing
public import Mathlib.NumberTheory.Padics.RingHoms
public import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.TowerScalarSingleCounit

/-! # Exactness of finite-free coefficient extension on tower systems

The coefficient extension `Z/l^(n+1) → O_E/l^(n+1)` is finite free, so ordinary scalar
extension of coefficient systems is exact and its universal derived counit is invertible.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
open scoped TensorProduct
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Every quotient `ZMod (p ^ k)` with `k ≥ 1` is a local ring. -/
theorem zmod_primePow_isLocalRing (p : ℕ) [hp : Fact p.Prime] (k : ℕ) :
    IsLocalRing (ZMod (p ^ (k + 1))) := by
  have : Fact (1 < p ^ (k + 1)) := ⟨Nat.one_lt_pow (Nat.succ_ne_zero k) hp.out.one_lt⟩
  exact IsLocalRing.of_surjective' (PadicInt.toZModPow (p := p) (k + 1))
    (ZMod.ringHom_surjective _)


theorem coefficientQuotient_ker (n : ℕ) (x : Padic.coefficientExtensionIntegers l E)
    (hx : Ideal.Quotient.mk (spEllIdeal l E ^ (n + 1)) x = 0) :
    x ∈ ((Ideal.span {((l ^ (n + 1) : ℕ) : ℤ)} : Ideal ℤ) •
      (⊤ : Submodule ℤ (Padic.coefficientExtensionIntegers l E))) := by
  rw [Ideal.Quotient.eq_zero_iff_mem, spEllIdeal, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [Submodule.ideal_span_singleton_smul]
  have h := Submodule.smul_mem_pointwise_smul y (((l ^ (n + 1) : ℕ) : ℤ))
    (⊤ : Submodule ℤ (Padic.coefficientExtensionIntegers l E)) Submodule.mem_top
  convert h using 1
  rw [zsmul_eq_mul]
  push_cast
  rfl

theorem coefficientIntegers_charZero : CharZero (Padic.coefficientExtensionIntegers l E) := by
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap (Padic l) E).injective
  refine ⟨fun a b h ↦ ?_⟩
  have h' := congrArg Subtype.val h
  simpa using h'

theorem coefficientIntegers_flat : Module.Flat ℤ (Padic.coefficientExtensionIntegers l E) := by
  have := coefficientIntegers_charZero l E
  infer_instance

/-- The integer-linear identification `ZMod (l ^ (n + 1)) ⊗ O_E ≃ O_E / l^(n+1)`. -/
def coefficientTensorEquiv (n : ℕ) :
    (ZMod (l ^ (n + 1)) ⊗[ℤ] Padic.coefficientExtensionIntegers l E) ≃ₗ[ℤ]
      SpTowerShriek.R l E n := by
  let O := Padic.coefficientExtensionIntegers l E
  let I : Ideal ℤ := Ideal.span {((l ^ (n + 1) : ℕ) : ℤ)}
  let e₁ : ZMod (l ^ (n + 1)) ⊗[ℤ] O ≃ₗ[ℤ] (ℤ ⧸ I) ⊗[ℤ] O :=
    LinearEquiv.rTensor O
      (Int.quotientSpanNatEquivZMod (l ^ (n + 1))).symm.toAddEquiv.toIntLinearEquiv
  let e₂ := TensorProduct.quotTensorEquivQuotSMul O I
  let f : O ⧸ (I • (⊤ : Submodule ℤ O)) →ₗ[ℤ] SpTowerShriek.R l E n :=
    Submodule.liftQ _ (Ideal.Quotient.mk (spEllIdeal l E ^ (n + 1))).toAddMonoidHom.toIntLinearMap
      (by
        rw [Submodule.ideal_span_singleton_smul]
        rintro _ ⟨y, -, rfl⟩
        simp only [LinearMap.mem_ker]
        change Ideal.Quotient.mk _ ((((l ^ (n + 1) : ℕ) : ℤ)) • y) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem, spEllIdeal, Ideal.span_singleton_pow,
          Ideal.mem_span_singleton, zsmul_eq_mul]
        push_cast
        exact dvd_mul_right _ _)
  have hf : Function.Bijective f := by
    constructor
    · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro z hz
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      rw [Submodule.Quotient.mk_eq_zero]
      exact coefficientQuotient_ker l E n x hz
    · intro z
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
      exact ⟨Submodule.Quotient.mk x, rfl⟩
  exact e₁ ≪≫ₗ e₂ ≪≫ₗ LinearEquiv.ofBijective f hf

/-- The quotient algebra structure on the actual coefficient ring. -/
abbrev coefficientZModAlgebra (n : ℕ) : Algebra (ZMod (l ^ (n + 1))) (SpTowerShriek.R l E n) :=
  (ZMod.castHom (ringChar.dvd (coefficient_annihilates l E n)) (SpTowerShriek.R l E n)).toAlgebra

theorem coefficient_zmod_free (n : ℕ) [Finite (SpTowerShriek.R l E n)] :
    letI := coefficientZModAlgebra l E n
    Module.Free (ZMod (l ^ (n + 1))) (SpTowerShriek.R l E n) := by
  let := coefficientZModAlgebra l E n
  have := coefficientIntegers_flat l E
  have := zmod_primePow_isLocalRing l n
  let T := coefficientTensorEquiv l E n
  let e : (ZMod (l ^ (n + 1)) ⊗[ℤ] Padic.coefficientExtensionIntegers l E)
      ≃ₗ[ZMod (l ^ (n + 1))]
      SpTowerShriek.R l E n :=
    { T.toAddEquiv.toAddMonoidHom.toZModLinearMap (l ^ (n + 1)) with
      invFun := T.symm
      left_inv := T.left_inv
      right_inv := T.right_inv }
  have : Module.Flat (ZMod (l ^ (n + 1))) (SpTowerShriek.R l E n) :=
    Module.Flat.of_linearEquiv e.symm
  have : Module.Finite (ZMod (l ^ (n + 1))) (SpTowerShriek.R l E n) := Module.Finite.of_finite
  exact Module.free_of_flat_of_isLocalRing

/-- A level scalar-extension functor, with its adjunction to restriction. -/
theorem exists_levelExtension (T : Scheme.{u}) (n : ℕ) :
    ∃ (G : SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        ((Rrings l T).obj (op n)) ⥤
        SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
          (SpTowerShriek.B l E T n))
      (h : ∀ M, G.obj M = SheafOfModules.changeOfRings (coefficientMap l E T n) M),
      (∀ {M N} (f : M ⟶ N), G.map f = eqToHom (h M) ≫
          SheafOfModules.changeOfRingsHom (coefficientMap l E T n) M f ≫
            eqToHom (h N).symm) ∧ G.Additive ∧
      Nonempty (G ⊣ SemilinearSections.res (coefficientMap l E T n)) := by
  let J := Scheme.ProEt.topology T
  let α := coefficientMap l E T n
  let := HasDerivedCategory.standard
    (SemilinearSections.Mod.{u + 1, u, u + 1} J ((Rrings l T).obj (op n)))
  let := HasDerivedCategory.standard
    (SemilinearSections.Mod.{u + 1, u, u + 1} J (SpTowerShriek.B l E T n))
  obtain ⟨D⟩ := SheafOfModules.nonempty_derivedChangeOfRingsCochainModel (J := J) α
  obtain ⟨_, _, ha⟩ := SheafOfModules.sheafRingCoefficientOrdinaryAdjunction (J := J) α
  obtain ⟨a, -⟩ := ha D.E D.obj_eq D.map_eq
  exact ⟨D.E, D.obj_eq, D.map_eq, inferInstance, ⟨a⟩⟩

/-- The unital quotient ring map underlying `coefficientMap`. -/
abbrev levelRingHom (n : ℕ) :
    ULift.{u + 1} (ZMod (l ^ (n + 1))) →+* ULift.{u + 1} (SpTowerShriek.R l E n) :=
  ULift.ringEquiv.{u, u + 1}.symm.toRingHom.comp
    ((ZMod.castHom (ringChar.dvd (coefficient_annihilates l E n))
      (SpTowerShriek.R l E n)).comp ULift.ringEquiv.{0, u + 1}.toRingHom)

theorem levelRing_free (n : ℕ) [Finite (SpTowerShriek.R l E n)] :
    letI := (levelRingHom l E n).toAlgebra
    Module.Free (ULift.{u + 1} (ZMod (l ^ (n + 1)))) (ULift.{u + 1} (SpTowerShriek.R l E n)) ∧
      Module.Finite (ULift.{u + 1} (ZMod (l ^ (n + 1))))
        (ULift.{u + 1} (SpTowerShriek.R l E n)) := by
  let := (levelRingHom l E n).toAlgebra
  have hfree := coefficient_zmod_free l E n
  let := coefficientZModAlgebra l E n
  let σ : ZMod (l ^ (n + 1)) ≃+* ULift.{u + 1} (ZMod (l ^ (n + 1))) := ULift.ringEquiv.symm
  have : RingHomInvPair σ.toRingHom σ.symm.toRingHom := RingHomInvPair.of_ringEquiv σ
  have : RingHomInvPair σ.symm.toRingHom σ.toRingHom := RingHomInvPair.symm _ _
  let e : SpTowerShriek.R l E n ≃ₛₗ[σ.toRingHom]
      ULift.{u + 1} (SpTowerShriek.R l E n) :=
    { toFun := ULift.up
      invFun := ULift.down
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun c x ↦ (rfl : ULift.up (c • x) = (σ c) • ULift.up x)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  exact ⟨Module.Free.of_equiv e, Module.Finite.of_finite⟩

/-- The level scalar extension along the actual finite quotient is exact. -/
theorem levelExtension_exact (T : Scheme.{u}) (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (G : SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        ((Rrings l T).obj (op n)) ⥤
        SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
          (SpTowerShriek.B l E T n))
    (h : ∀ M, G.obj M = SheafOfModules.changeOfRings (coefficientMap l E T n) M)
    (hm : ∀ {M N} (f : M ⟶ N), G.map f = eqToHom (h M) ≫
          SheafOfModules.changeOfRingsHom (coefficientMap l E T n) M f ≫
            eqToHom (h N).symm)
    (a : G ⊣ SemilinearSections.res (coefficientMap l E T n)) :
    PreservesFiniteLimits G ∧ PreservesFiniteColimits G := by
  let : Algebra (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))
      (CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R l E n))) :=
    (levelRingHom l E n).toAlgebra
  obtain ⟨_, _⟩ := levelRing_free l E n
  refine ⟨CategoryTheory.constantFiniteFree_extensionLeftExact (Scheme.ProEt.topology T)
    (CommRingCat.of (ULift.{u + 1} (ZMod (l ^ (n + 1)))))
    (CommRingCat.of (ULift.{u + 1} (SpTowerShriek.R l E n))) G h hm, ?_⟩
  have := a.leftAdjoint_preservesColimits
  infer_instance

section Evaluation

attribute [local irreducible] SemilinearSections.systemRing
  SemilinearSections.ringPresheaf SemilinearSections.rings
set_option backward.defeqAttrib.useBackward true

/-- Ordinary scalar extension of systems commutes with evaluation at every level:
the inverse mate of the identity restriction comparison is invertible. -/
theorem scalarEvaluationMate_isIso_generic
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    [EssentiallySmall.{u + 1} C]
    (B F : ℕ → Sheaf J CommRingCat.{u + 1})
    (τ : ∀ n, B (n + 1) ⟶ B n) (σ : ∀ n, F (n + 1) ⟶ F n)
    (α : ∀ n, B n ⟶ F n) (hα : ∀ n, α (n + 1) ≫ σ n = τ n ≫ α n)
    (S : SemilinearSections.ScalarData.{u + 1, u, u + 1}
      (SemilinearSections.systemMap J B τ F σ α hα)) (n : ℕ)
    (G : SemilinearSections.Mod.{u + 1, u, u + 1} J (B n) ⥤
      SemilinearSections.Mod.{u + 1, u, u + 1} J (F n))
    (a : G ⊣ SemilinearSections.res (α n)) :
    IsIso ((mateEquiv S.ordinaryAdjunction a).symm
      (SemilinearSections.restrictionEvaluation_existsUnique.{u + 1, u, u + 1}
        J B τ F σ α hα n).exists.choose.hom).natTrans := by
  let : ((𝟭 ℕ).prod (𝟭 C)).IsContinuous
      (coefficientSequenceTopology J) (coefficientSequenceTopology J) := by
    change (𝟭 (ℕ × C)).IsContinuous _ _
    infer_instance
  let a₀ := (sheafCompose (coefficientSequenceTopology J)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
    (SemilinearSections.systemMap J B τ F σ α hα)
  let b₀ := (sheafCompose J
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (α n)
  have hs : SheafOfModules.pushforward (F := (𝟭 ℕ).prod (𝟭 C)) a₀ =
      SemilinearSections.res (SemilinearSections.systemMap J B τ F σ α hα) := by
    rfl
  have hl : SheafOfModules.pushforward (F := 𝟭 C) b₀ =
      SemilinearSections.res (α n) := by
    rfl
  let as' : S.model.E ⊣ SheafOfModules.pushforward
      (F := (𝟭 ℕ).prod (𝟭 C)) a₀ := by
    rw [hs]
    exact S.ordinaryAdjunction
  let al' : G ⊣ SheafOfModules.pushforward (F := 𝟭 C) b₀ := by
    rw [hl]
    exact a
  have hd := SequenceModuleEvaluation.sequenceModulePullbackEvaluation_isIso
    J J (𝟭 C)
    (SemilinearSections.ring _ (SemilinearSections.systemRing J B τ))
    (SemilinearSections.ring _ (SemilinearSections.systemRing J F σ)) n a₀
    (SemilinearSections.ring J (B n)) (SemilinearSections.ring J (F n))
    (SemilinearSections.evaluation_ring J B τ n)
    (SemilinearSections.evaluation_ring J F σ n) b₀
    S.model.E G as' al'
    (by rw [hs, hl]; exact (SemilinearSections.restrictionEvaluation_existsUnique.{u + 1, u, u + 1}
        J B τ F σ α hα n).exists.choose)
  convert hd using 1 <;> rfl

end Evaluation

/-- The identity-on-sections comparison between restriction and evaluation. -/
abbrev restrictionEvaluation (T : Scheme.{u}) (n : ℕ) :=
  (SemilinearSections.restrictionEvaluation_existsUnique.{u + 1, u, u + 1}
    (Scheme.ProEt.topology T) (fun n ↦ (Rrings l T).obj (op n))
    (fun n ↦ (Rrings l T).map (homOfLE (Nat.le_succ n)).op)
    (SpTowerShriek.B l E T) (SpTowerShriek.tau l E T) (coefficientMap l E T)
    (coefficientMap_transition l E T) n).exists.choose

/-- Ordinary scalar extension of systems commutes with evaluation at every level. -/
theorem scalarEvaluationMate_isIso {T : Scheme.{u}} (c : Chern l E T) (n : ℕ)
    (G : SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
        ((Rrings l T).obj (op n)) ⥤
        SemilinearSections.Mod.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
          (SpTowerShriek.B l E T n))
    (a : G ⊣ SemilinearSections.res (coefficientMap l E T n)) :
    IsIso ((mateEquiv c.scalar.ordinaryAdjunction a).symm
      (restrictionEvaluation l E T n).hom).natTrans :=
  scalarEvaluationMate_isIso_generic (Scheme.ProEt.topology T)
    (fun n ↦ (Rrings l T).obj (op n)) (SpTowerShriek.B l E T)
    (fun n ↦ (Rrings l T).map (homOfLE (Nat.le_succ n)).op) (SpTowerShriek.tau l E T)
    (coefficientMap l E T) (coefficientMap_transition l E T) c.scalar n G a

/-- Ordinary scalar extension of coefficient systems is exact: the coefficient
extension is finite free at every level. -/
theorem scalarExtension_exact {T : Scheme.{u}} (c : Chern l E T)
    [∀ n, Finite (SpTowerShriek.R l E n)] :
    PreservesFiniteLimits c.scalar.model.E ∧ PreservesFiniteColimits c.scalar.model.E := by
  have hfaith : JointlyFaithful (SpTowerShriek.ev l E T) := by
    constructor
    intro M N f h hfh
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    rintro ⟨n, V⟩
    ext x
    exact congrArg (fun k ↦ k.val.app (op V) x) (hfh n)
  let G := fun n ↦ (exists_levelExtension l E T n).choose
  have hG (n : ℕ) := (exists_levelExtension l E T n).choose_spec
  have : ∀ n, (G n).Additive := fun n ↦ (hG n).choose_spec.2.1
  have hadj (n : ℕ) : Nonempty (G n ⊣ SemilinearSections.res (coefficientMap l E T n)) :=
    (hG n).choose_spec.2.2
  have hex (n : ℕ) : exactFunctor _ _ (G n) :=
    levelExtension_exact l E T n (G n) (hG n).choose (hG n).choose_spec.1 (hadj n).some
  have hiso (n : ℕ) := scalarEvaluationMate_isIso l E c n (G n) (hadj n).some
  have := hfaith.jointlyReflectsIsomorphisms.exactFunctor_of_iso c.scalar.model.E
    G hex (fun n ↦ (asIso ((mateEquiv c.scalar.ordinaryAdjunction (hadj n).some).symm
      (restrictionEvaluation l E T n).hom).natTrans).symm)
  exact this

/-- The universal derived scalar counit is invertible on every complex. -/
theorem scalarCounit_isIso {T : Scheme.{u}} (c : Chern l E T)
    [∀ n, Finite (SpTowerShriek.R l E n)] : IsIso c.scalar.model.ε := by
  obtain ⟨_, _⟩ := scalarExtension_exact l E c
  have := c.scalar.model.universal
  apply Functor.isIso_of_isLeftDerivedFunctor_of_inverts
    (W := HomologicalComplex.quasiIso _ (.up ℤ)) c.scalar.model.T c.scalar.model.ε
  intro K L f hf
  have : QuasiIso f := hf
  have : QuasiIso ((c.scalar.model.E.mapHomologicalComplex (.up ℤ)).map f) := inferInstance
  exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 this

/-- Consequently the scalar counit on degree-zero systems is invertible. -/
theorem scalarSingleCounit_isIso {T : Scheme.{u}} (c : Chern l E T)
    [∀ n, Finite (SpTowerShriek.R l E n)] : IsIso (scalarSingleCounit c) := by
  have := scalarCounit_isIso l E c
  unfold scalarSingleCounit
  infer_instance


/-- The ordinary adjunction transpose of a single-complex map, computed in degree zero. -/
theorem single_adjunct
    {C : Type*} [Category C] [Abelian C] {D : Type*} [Category D] [Abelian D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    (adj : F ⊣ G) {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    ((adj.mapHomologicalComplex (.up ℤ)).homEquiv
      ((HomologicalComplex.single C (.up ℤ) 0).obj X)
      ((HomologicalComplex.single D (.up ℤ) 0).obj Y))
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app X ≫
          (HomologicalComplex.single D (.up ℤ) 0).map f) ≫
        (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app Y =
      (HomologicalComplex.single C (.up ℤ) 0).map ((adj.homEquiv X Y) f) := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [Adjunction.homEquiv_unit, HomologicalComplex.comp_f,
    Adjunction.mapHomologicalComplex_unit_app_f, Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.single_map_f_self, Functor.map_comp, Category.assoc]
  simp only [← G.map_comp_assoc, Iso.inv_hom_id_assoc]
  rw [G.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  erw [← adj.unit.naturality_assoc]
  rfl

/-- The representative transpose equation of the scalar adjunction holds on every
complex, not only on K-flat ones: resolve by a K-flat complex and cancel the
inverted resolution map. -/
theorem scalarTranspose_any {T : Scheme.{u}} (c : Chern l E T)
    (P : CochainComplex (Systems T (Rrings l T)) ℤ)
    (Q : CochainComplex (Systems T (Arings l E T)) ℤ)
    (f : (c.scalar.model.E.mapHomologicalComplex (.up ℤ)).obj P ⟶ Q) :
    (c.scalar.adjunction.homEquiv _ _) (c.scalar.model.ε.app P ≫ DerivedCategory.Q.map f) ≫
        (Functor.mapDerivedCategoryFactors (SemilinearSections.res.{u + 1, u, u + 1}
          (coefficientSystemMap l E T))).hom.app Q =
      DerivedCategory.Q.map
        (((c.scalar.ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P Q) f) := by
  obtain ⟨K, π, hK, -, hπ, -⟩ :=
    CochainComplex.exists_isKFlatResolutionIndependentCoefficients P
  have h := c.scalar.transpose_model K Q hK
    ((c.scalar.model.E.mapHomologicalComplex (.up ℤ)).map π ≫ f)
  have hn := c.scalar.model.ε.naturality π
  simp only [Functor.comp_map] at hn
  rw [Functor.map_comp, ← Category.assoc, ← hn, Category.assoc,
    Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left,
    Functor.map_comp, Category.assoc] at h
  have : IsIso (DerivedCategory.Q.map π) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ π).2 hπ
  exact (cancel_epi (DerivedCategory.Q.map π)).mp h


/-- Generic single-complex transpose: if the derived adjunction transposes every
representative map as the ordinary adjunction does, then on single complexes the
transpose of the single counit followed by a degree-zero map is the ordinary adjunct. -/
theorem _root_.CategoryTheory.Adjunction.single_transpose_of_derived
    {C₁ C₂ : Type*} [Category C₁] [Category C₂] [Abelian C₁] [Abelian C₂]
    [HasDerivedCategory C₁] [HasDerivedCategory C₂]
    {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₁} [F.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (adj : F ⊣ G) (T : DerivedCategory C₁ ⥤ DerivedCategory C₂)
    (ε : DerivedCategory.Q ⋙ T ⟶ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (dadj : T ⊣ G.mapDerivedCategory)
    (h : ∀ (P : CochainComplex C₁ ℤ) (Q : CochainComplex C₂ ℤ)
      (f : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶ Q),
      (dadj.homEquiv _ _) (ε.app P ≫ DerivedCategory.Q.map f) ≫
          G.mapDerivedCategoryFactors.hom.app Q =
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv P Q f))
    (X : C₁) (Y : C₂) (f : F.obj X ⟶ Y) :
    (dadj.homEquiv _ _) (T.map ((DerivedCategory.singleFunctorIsoCompQ C₁ 0).hom.app X) ≫
        ε.app ((HomologicalComplex.single C₁ (.up ℤ) 0).obj X) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app X) ≫
        (DerivedCategory.singleFunctorIsoCompQ C₂ 0).inv.app (F.obj X) ≫
        (DerivedCategory.singleFunctor C₂ 0).map f) ≫
      (G.mapDerivedCategorySingleFunctor 0).hom.app Y =
    (DerivedCategory.singleFunctor C₁ 0).map (adj.homEquiv X Y f) := by
  have hs : (DerivedCategory.singleFunctor C₂ 0).map f =
      DerivedCategory.Q.map ((HomologicalComplex.single C₂ (.up ℤ) 0).map f) := rfl
  have h₁ := h _ _ ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app X ≫
    (HomologicalComplex.single C₂ (.up ℤ) 0).map f)
  have h₂ := single_adjunct adj f
  have hG : (G.mapDerivedCategorySingleFunctor 0).hom.app Y =
      G.mapDerivedCategoryFactors.hom.app ((HomologicalComplex.single C₂ (.up ℤ) 0).obj Y) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app Y) := by
    dsimp [Functor.mapDerivedCategorySingleFunctor, DerivedCategory.singleFunctorIsoCompQ]
    simp
    rfl
  dsimp only [DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  erw [T.map_id, Category.id_comp, Category.id_comp]
  rw [hs, ← Functor.map_comp, hG, ← Category.assoc]
  erw [h₁]
  rw [← Functor.map_comp, h₂]
  rfl

/-- The derived scalar adjunct of the single counit followed by a degree-zero map is
the single of the ordinary adjunct. -/
theorem scalarSingleCounit_transpose {T : Scheme.{u}} (c : Chern l E T)
    (M : Systems T (Rrings l T)) (Y : Systems T (Arings l E T))
    (f : c.scalar.model.E.obj M ⟶ Y) :
    (c.scalar.adjunction.homEquiv _ _)
        ((scalarSingleCounit c).app M ≫
          (DerivedCategory.singleFunctor (Systems T (Arings l E T)) 0).map f) ≫
      ((WeilConjectures.SemilinearSections.res
        (coefficientSystemMap l E T)).mapDerivedCategorySingleFunctor 0).hom.app Y =
    (DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).map
      (c.scalar.ordinaryAdjunction.homEquiv M Y f) := by
  have h := Adjunction.single_transpose_of_derived c.scalar.ordinaryAdjunction c.scalar.T
    c.scalar.model.ε c.scalar.adjunction (scalarTranspose_any l E c) M Y f
  simp only [scalarSingleCounit, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Category.assoc]
  exact h

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
