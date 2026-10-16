/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D4
-/
module

public import Sheaf.Paper.ContinuousIntegralCoefficients
public import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Sheaf.Paper.IntegralConstructibleKernels
import all Sheaf.Paper.IntegralMatrixEntryProperties
import Sheaf.Paper.FiniteDiscreteCondensedRing
import Sheaf.Paper.FiniteDiscreteSchemeRing
import Sheaf.Paper.ContinuousRegularFunctions
import Sheaf.Paper.ContinuousCoefficientRealizations
import Mathlib.CategoryTheory.Sites.Adjunction
import Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import Sheaf.Paper.FiniteBiproductPivot
import Sheaf.Paper.GeometricFieldProEtaleEvaluation
import Sheaf.Paper.IntegralMatrixAnalyticCover

/-! # Local integral torsion and quotient charts -/

@[expose] public section

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Obj

attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] comp_preservesFiniteLimits comp_preservesLimits

-- Cokernels of diagonal blocks, and integral elimination when the pivot divides its column.
private noncomputable def diagonalCokernelIso
    {C : Type*} [Category C] [Abelian C] {A B D E : C}
    (p : A ⟶ D) (s : B ⟶ E) :
    cokernel (biprod.map p s) ≅ cokernel p ⊞ cokernel s := by
  let f := biprod.map p s
  let q := biprod.map (cokernel.π p) (cokernel.π s)
  have hfq : f ≫ q = 0 := by ext <;> simp [f, q]
  let a := cokernel.desc f q hfq
  have hp : p ≫ biprod.inl ≫ cokernel.π f = 0 := by
    simpa only [f, biprod.inl_map_assoc, Limits.comp_zero] using
      biprod.inl ≫= cokernel.condition f
  have hs : s ≫ biprod.inr ≫ cokernel.π f = 0 := by
    simpa only [f, biprod.inr_map_assoc, Limits.comp_zero] using
      biprod.inr ≫= cokernel.condition f
  let b := biprod.desc (cokernel.desc p (biprod.inl ≫ cokernel.π f) hp)
    (cokernel.desc s (biprod.inr ≫ cokernel.π f) hs)
  refine ⟨a, b, ?_, ?_⟩
  · change a ≫ b = 𝟙 _
    apply (cancel_epi (cokernel.π f)).mp
    apply biprod.hom_ext' <;> simp [a, b, q]
  · change b ≫ a = 𝟙 _
    apply biprod.hom_ext'
    · apply (cancel_epi (cokernel.π p)).mp
      simp [a, b, q]
    · apply (cancel_epi (cokernel.π s)).mp
      simp [a, b, q]

private noncomputable def integralPivotCokernelIso
    {C : Type*} [Category C] [Abelian C] {A B D E : C}
    (p : A ⟶ D) (r : B ⟶ A) (s : D ⟶ E) (d : B ⟶ E) :
    cokernel (biprod.lift (biprod.desc p (r ≫ p)) (biprod.desc (p ≫ s) d)) ≅
      cokernel p ⊞ cokernel (d - r ≫ p ≫ s) := by
  let U : A ⊞ B ≅ A ⊞ B :=
    { hom := biprod.lift (biprod.desc (𝟙 A) r) biprod.snd
      inv := biprod.lift (biprod.desc (𝟙 A) (-r)) biprod.snd
      hom_inv_id := by ext <;> simp
      inv_hom_id := by ext <;> simp }
  let V : D ⊞ E ≅ D ⊞ E :=
    { hom := biprod.lift biprod.fst (biprod.desc (-s) (𝟙 E))
      inv := biprod.lift biprod.fst (biprod.desc s (𝟙 E))
      hom_inv_id := by ext <;> simp
      inv_hom_id := by ext <;> simp }
  refine cokernel.mapIso _ (biprod.map p (d - r ≫ p ≫ s)) U V ?_ ≪≫
    diagonalCokernelIso p (d - r ≫ p ≫ s)
  ext <;> simp [U, V, biprod.lift_eq, biprod.desc_eq,
    Preadditive.comp_add, Preadditive.add_comp, sub_eq_add_neg, add_comm]

private noncomputable def finiteDiagonalCokernelIso
    {C : Type*} [Category C] [Abelian C] {ι : Type} [Fintype ι]
    (A B : ι → C) (f : ∀ i, A i ⟶ B i) :
    cokernel (biproduct.map f) ≅ ⨁ fun i ↦ cokernel (f i) := by
  classical
  let g := biproduct.map f
  let q := biproduct.map (fun i ↦ cokernel.π (f i))
  have hgq : g ≫ q = 0 := by
    apply biproduct.hom_ext'
    intro i
    simp [g, q]
  let a := cokernel.desc g q hgq
  have hf (i : ι) : f i ≫ biproduct.ι B i ≫ cokernel.π g = 0 := by
    simpa only [g, biproduct.ι_map_assoc, Limits.comp_zero] using
      biproduct.ι A i ≫= cokernel.condition g
  let b := biproduct.desc (fun i ↦ cokernel.desc (f i)
    (biproduct.ι B i ≫ cokernel.π g) (hf i))
  refine ⟨a, b, ?_, ?_⟩
  · change a ≫ b = 𝟙 _
    apply (cancel_epi (cokernel.π g)).mp
    apply biproduct.hom_ext'
    intro i
    simp [a, b, q]
  · change b ≫ a = 𝟙 _
    apply biproduct.hom_ext'
    intro i
    apply (cancel_epi (cokernel.π (f i))).mp
    simp [a, b, q]

private noncomputable def scalarImageBiprodIso
    {C : Type*} [Category C] [Abelian C] (n : ℕ) (M T : C)
    [Mono (n • 𝟙 M)] (hT : n • 𝟙 T = 0) :
    image (n • 𝟙 (M ⊞ T)) ≅ M := by
  let q : M ⊞ T ⟶ M := biprod.fst
  let m : M ⟶ M ⊞ T := (n • 𝟙 M) ≫ biprod.inl
  have : Epi q := by dsimp only [q]; infer_instance
  have : Mono m := by dsimp only [m]; infer_instance
  have : StrongEpi q := strongEpi_of_epi q
  refine (image.isoStrongEpiMono q m ?_).symm
  apply biprod.hom_ext <;> apply biprod.hom_ext'
  · simp [q, m]
  · simp [q, m]
  · simp [q, m]
  · simpa [q, m] using hT.symm

private noncomputable def scalarCokernelBiprodIso
    {C : Type*} [Category C] [Abelian C] (n : ℕ) (M T : C)
    (hT : n • 𝟙 T = 0) :
    cokernel (n • 𝟙 (M ⊞ T)) ≅ cokernel (n • 𝟙 M) ⊞ T := by
  have he : n • 𝟙 (M ⊞ T) = biprod.map (n • 𝟙 M) (n • 𝟙 T) := by
    ext <;> simp
  exact cokernelIsoOfEq he ≪≫ diagonalCokernelIso _ _ ≪≫
    biprod.mapIso (Iso.refl _) (cokernelIsoOfEq hT ≪≫ cokernelZeroIsoTarget)

private lemma scalarBoundFiniteBiproduct {C : Type*} [Category C] [Abelian C]
    (r : ℕ) (M : Fin r → C) (k : ℕ → ℕ)
    (hM : ∀ i, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → k n • 𝟙 (M i) = 0) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → k n • 𝟙 (⨁ M) = 0 := by
  classical
  choose N hN using hM
  refine ⟨Finset.univ.sup N, fun n hn ↦ ?_⟩
  apply biproduct.hom_ext'
  intro i
  have hi : N i ≤ n := (Finset.le_sup (f := N) (Finset.mem_univ i)).trans hn
  have hzero := hN i n hi =≫ biproduct.ι M i
  simpa only [Preadditive.nsmul_comp, Category.id_comp, Preadditive.comp_nsmul,
    Category.comp_id, Limits.zero_comp, Limits.comp_zero] using hzero

namespace AlgebraicGeometry.ProEtale.CondensedRing

private lemma constantNormNeighborhood (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (T : Type*) [TopologicalSpace T] (f : C(T, E)) (x : T) (hx : f x ≠ 0) :
    ∃ U : TopologicalSpace.Opens T, x ∈ U ∧ ∀ y ∈ U, ‖f y‖ = ‖f x‖ := by
  let : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra ℚ_[ℓ]
  let U : TopologicalSpace.Opens T :=
    ⟨f ⁻¹' Metric.ball (f x) ‖f x‖, Metric.isOpen_ball.preimage f.continuous⟩
  refine ⟨U, Metric.mem_ball_self (norm_pos_iff.mpr hx), ?_⟩
  intro y hy
  have hlt : ‖f y - f x‖ < ‖f x‖ := by
    change dist (f y) (f x) < ‖f x‖ at hy
    simpa only [dist_eq_norm] using hy
  have he : ‖f y + -f x‖ < max ‖f y‖ ‖-f x‖ := by
    simpa only [norm_neg, sub_eq_add_neg] using hlt.trans_le (le_max_right ‖f y‖ ‖f x‖)
  simpa only [norm_neg] using IsUltrametricDist.norm_eq_of_add_norm_lt_max he

-- The finite quotients required by the integral chart calculation.
private lemma integralPrincipalQuotientDiscrete (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (a : continuousIntegers ℓ E) (ha : a ≠ 0) :
    DiscreteTopology ((continuousIntegers ℓ E) ⧸ Ideal.span {a}) := by
  let I : Ideal (continuousIntegers ℓ E) := Ideal.span {a}
  have ha' : (a : E) ≠ 0 := fun h ↦ ha (Subtype.ext h)
  have hopen : IsOpen (I : Set (continuousIntegers ℓ E)) := by
    apply I.toAddSubgroup.isOpen_of_mem_nhds (g := 0)
    have ho : IsOpen ((fun x : continuousIntegers ℓ E ↦ (x : E)) ⁻¹'
        Metric.ball 0 ‖(a : E)‖) := Metric.isOpen_ball.preimage continuous_subtype_val
    apply Filter.mem_of_superset (ho.mem_nhds (by
      change dist (0 : E) 0 < ‖(a : E)‖
      simpa only [dist_self] using norm_pos_iff.mpr ha'))
    intro x hx
    have hx' : ‖(x : E)‖ < ‖(a : E)‖ := by
      change dist (x : E) 0 < ‖(a : E)‖ at hx
      simpa only [dist_zero_right] using hx
    have hdiv : (x : E) / a ∈ continuousIntegers ℓ E := by
      change ‖(x : E) / a‖₊ ≤ 1
      rw [← NNReal.coe_le_coe, NNReal.coe_one, coe_nnnorm, norm_div]
      exact (div_le_one (norm_pos_iff.mpr ha')).2 hx'.le
    change x ∈ Ideal.span {a}
    rw [Ideal.mem_span_singleton]
    refine ⟨⟨(x : E) / a, hdiv⟩, ?_⟩
    apply Subtype.ext
    change (x : E) = (a : E) * ((x : E) / a)
    exact (mul_div_cancel₀ _ ha').symm
  exact QuotientAddGroup.discreteTopology hopen

private lemma integralPrincipalQuotientFinite (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E]
    (a : continuousIntegers ℓ E) (ha : a ≠ 0) :
    Finite ((continuousIntegers ℓ E) ⧸ Ideal.span {a}) := by
  let : DiscreteTopology ((continuousIntegers ℓ E) ⧸ Ideal.span {a}) :=
    integralPrincipalQuotientDiscrete ℓ E a ha
  let : ProperSpace E := FiniteDimensional.proper ℚ_[ℓ] E
  have hball : (continuousIntegers ℓ E : Set E) = Metric.closedBall 0 1 := by
    ext x
    change ‖x‖₊ ≤ 1 ↔ dist x 0 ≤ 1
    simp only [dist_zero_right, ← NNReal.coe_le_coe, NNReal.coe_one]
    rfl
  let : CompactSpace (continuousIntegers ℓ E) :=
    isCompact_iff_compactSpace.mp (hball ▸ isCompact_closedBall 0 1)
  exact finite_of_compact_of_discrete

private lemma integralPrincipalQuotientFunctionsSurjective (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (a : continuousIntegers ℓ E) (ha : a ≠ 0)
    (S : Type u) [TopologicalSpace S] :
    Function.Surjective ((Ideal.Quotient.mk (Ideal.span {a})).compLeftContinuous S
      continuous_quot_mk) := by
  classical
  let : DiscreteTopology ((continuousIntegers ℓ E) ⧸ Ideal.span {a}) :=
    integralPrincipalQuotientDiscrete ℓ E a ha
  intro f
  let σ : (continuousIntegers ℓ E) ⧸ Ideal.span {a} → continuousIntegers ℓ E := Quotient.out
  have hσ : Continuous σ := continuous_of_discreteTopology
  refine ⟨⟨fun x ↦ σ (f x), hσ.comp f.continuous⟩, ?_⟩
  ext x
  exact Quotient.out_eq (f x)

private lemma integralPrincipalQuotientFunctionsKernel (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (a : continuousIntegers ℓ E) (ha : a ≠ 0)
    (S : Type u) [TopologicalSpace S] (f : C(S, continuousIntegers ℓ E))
    (hf : ((Ideal.Quotient.mk (Ideal.span {a})).compLeftContinuous S
      continuous_quot_mk) f = 0) :
    ∃ g : C(S, continuousIntegers ℓ E), ContinuousMap.const S a * g = f := by
  have ha' : (a : E) ≠ 0 := fun h ↦ ha (Subtype.ext h)
  have hdiv (x : S) : (f x : E) / a ∈ continuousIntegers ℓ E := by
    have hx : Ideal.Quotient.mk (Ideal.span {a}) (f x) = 0 :=
      congrArg (fun z : C(S, (continuousIntegers ℓ E) ⧸ Ideal.span {a}) ↦ z x) hf
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp ((Ideal.Quotient.eq_zero_iff_mem).mp hx)
    have he : (f x : E) = (a : E) * (b : E) := congrArg Subtype.val hb
    rw [he, mul_div_cancel_left₀ _ ha']
    exact b.property
  let g : C(S, continuousIntegers ℓ E) :=
    ⟨fun x ↦ ⟨(f x : E) / a, hdiv x⟩,
      ((continuous_subtype_val.comp f.continuous).div_const (a : E)).subtype_mk _⟩
  refine ⟨g, ?_⟩
  ext x
  change (a : E) * ((f x : E) / a) = (f x : E)
  exact mul_div_cancel₀ _ ha'

private lemma finiteContinuousRingSetConstant (X : Scheme.{u})
    (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]
    [DiscreteTopology B] [Finite B] :
    ∃ n : ℕ, Nonempty
      ((sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).obj
        (continuousAbRing X B) ≅
      (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj
        (ULift.{u + 1} (Fin n))) := by
  classical
  let : Fintype B := Fintype.ofFinite B
  obtain ⟨e, he⟩ := Profinite.finiteDiscreteCondensedRing_constant.{u} B
  obtain ⟨eX, _⟩ := finiteDiscreteSchemeRing_constant B X e he
  let eAb : (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} B)) ≅ continuousAbRing X B :=
    eX ≪≫ asIso (chartComparison X B)
  let eFin : ULift.{u + 1} B ≃ ULift.{u + 1} (Fin (Fintype.card B)) :=
    Equiv.ulift.trans ((Fintype.equivFin B).trans Equiv.ulift.symm)
  exact ⟨Fintype.card B, ⟨
    (sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).mapIso eAb.symm ≪≫
    (constantCommuteCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).app _ ≪≫
    (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).mapIso eFin.toIso⟩⟩

private lemma integralPrincipalQuotientSetConstant (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] (X : Scheme.{u})
    (a : continuousIntegers ℓ E) (ha : a ≠ 0) :
    ∃ n : ℕ, Nonempty
      ((sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).obj
        (continuousAbRing X ((continuousIntegers ℓ E) ⧸ Ideal.span {a})) ≅
      (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj
        (ULift.{u + 1} (Fin n))) := by
  let : DiscreteTopology ((continuousIntegers ℓ E) ⧸ Ideal.span {a}) :=
    integralPrincipalQuotientDiscrete ℓ E a ha
  let : Finite ((continuousIntegers ℓ E) ⧸ Ideal.span {a}) :=
    integralPrincipalQuotientFinite ℓ E a ha
  exact finiteContinuousRingSetConstant X _

-- Sectionwise division identifies the actual categorical principal cokernel.
private lemma integralPrincipalCokernelIso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (X : Scheme.{u}) (a : continuousIntegers ℓ E) (ha : a ≠ 0) :
    Nonempty
      ((Mod.forget (continuousAbRing X (continuousIntegers ℓ E))).obj
        (cokernel (continuousMultiplier X (continuousIntegers ℓ E)
          (ContinuousMap.const X a))) ≅
        continuousAbRing X ((continuousIntegers ℓ E) ⧸ Ideal.span {a})) := by
  let R := continuousAbRing X (continuousIntegers ℓ E)
  let J := Scheme.ProEt.topology X
  let p := continuousMultiplier X (continuousIntegers ℓ E) (ContinuousMap.const X a)
  let q : R ⟶ continuousAbRing X ((continuousIntegers ℓ E) ⧸ Ideal.span {a}) :=
    (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (continuousMapRingSheafMap X (Ideal.Quotient.mk (Ideal.span {a}))
        continuous_quot_mk)
  have hqa : Ideal.Quotient.mk (Ideal.span {a}) a = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton a))
  have hw : p.hom ≫ q = 0 := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    ext t
    change Ideal.Quotient.mk (Ideal.span {a}) (x.down t * a) = 0
    rw [map_mul, hqa, mul_zero]
  let S := ShortComplex.mk p.hom q hw
  have hsec (U : X.ProEtᵒᵖ) :
      (S.map (sheafToPresheaf J Ab.{u + 1} ⋙ (evaluation _ _).obj U)).ShortExact := by
    let T := S.map (sheafToPresheaf J Ab.{u + 1} ⋙ (evaluation _ _).obj U)
    have hm : Mono T.f := by
      rw [AddCommGrpCat.mono_iff_injective]
      intro x y hxy
      apply ULift.ext
      apply ContinuousMap.ext
      intro t
      have he := congrArg
        (fun z : ULift.{u + 1} C(U.unop.left, continuousIntegers ℓ E) ↦ z.down t) hxy
      change x.down t * a = y.down t * a at he
      exact mul_right_cancel₀ ha he
    have he : Epi T.g := by
      rw [AddCommGrpCat.epi_iff_surjective]
      intro y
      obtain ⟨x, hx⟩ := integralPrincipalQuotientFunctionsSurjective ℓ E a ha
        U.unop.left y.down
      exact ⟨ULift.up x, ULift.ext _ _ hx⟩
    have hex : T.Exact := by
      rw [ShortComplex.ab_exact_iff]
      intro x hx
      have hx' : ((Ideal.Quotient.mk (Ideal.span {a})).compLeftContinuous
          U.unop.left continuous_quot_mk) x.down = 0 := congrArg ULift.down hx
      obtain ⟨g, hg⟩ := integralPrincipalQuotientFunctionsKernel ℓ E a ha U.unop.left
        x.down hx'
      refine ⟨ULift.up g, ?_⟩
      apply ULift.ext
      apply ContinuousMap.ext
      intro t
      change g t * a = x.down t
      rw [mul_comm]
      exact congrArg (fun z : C(U.unop.left, continuousIntegers ℓ E) ↦ z t) hg
    exact ShortComplex.ShortExact.mk' hex hm he
  have hT : (S.map (sheafToPresheaf J Ab.{u + 1})).ShortExact := by
    let T := S.map (sheafToPresheaf J Ab.{u + 1})
    have : Mono T.f := by
      rw [NatTrans.mono_iff_mono_app]
      exact fun U ↦ (hsec U).mono_f
    have : Epi T.g := by
      rw [NatTrans.epi_iff_epi_app]
      exact fun U ↦ (hsec U).epi_g
    refine ShortComplex.ShortExact.mk' ?_ inferInstance inferInstance
    rw [ShortComplex.exact_iff_evaluation]
    exact fun U ↦ (hsec U).exact
  have hT' := hT.map_of_exact (presheafToSheaf J Ab.{u + 1})
  have hs : S.ShortExact := ShortComplex.shortExact_of_iso
    (ShortComplex.mapNatIso S (sheafificationNatIso J Ab.{u + 1})).symm hT'
  exact ⟨PreservesCokernel.iso (Mod.forget R) p ≪≫
    colimit.isoColimitCocone ⟨_, hs.gIsCokernel⟩⟩

private lemma integralPrincipalCokernelSetConstant (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] (X : Scheme.{u})
    (a : continuousIntegers ℓ E) (ha : a ≠ 0) :
    ∃ n : ℕ, Nonempty
      ((Mod.forget (continuousAbRing X (continuousIntegers ℓ E)) ⋙
          sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).obj
        (cokernel (continuousMultiplier X (continuousIntegers ℓ E)
          (ContinuousMap.const X a))) ≅
      (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj
        (ULift.{u + 1} (Fin n))) := by
  obtain ⟨e⟩ := integralPrincipalCokernelIso ℓ E X a ha
  obtain ⟨n, ⟨e'⟩⟩ := integralPrincipalQuotientSetConstant ℓ E X a ha
  exact ⟨n, ⟨(sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).mapIso e ≪≫ e'⟩⟩

-- A pivot with constant norm differs from a fixed coefficient by a continuous unit.
private lemma integralConstantNormCokernelIso (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (X : Scheme.{u}) (b : C(X, continuousIntegers ℓ E))
    (a : continuousIntegers ℓ E) (ha : a ≠ 0)
    (hb : ∀ x, ‖(b x : E)‖ = ‖(a : E)‖) :
    Nonempty (cokernel (continuousMultiplier X _ b) ≅
      cokernel (continuousMultiplier X _ (ContinuousMap.const X a))) := by
  have ha' : (a : E) ≠ 0 := fun h ↦ ha (Subtype.ext h)
  have hb' (x : X) : (b x : E) ≠ 0 := by
    intro h
    have he := hb x
    rw [h, norm_zero] at he
    exact ha' (norm_eq_zero.mp he.symm)
  have hu (x : X) : (b x : E) / a ∈ continuousIntegers ℓ E := by
    change ‖(b x : E) / a‖₊ ≤ 1
    rw [← NNReal.coe_le_coe, NNReal.coe_one, coe_nnnorm, norm_div, hb x]
    exact (div_le_one (norm_pos_iff.mpr ha')).2 le_rfl
  have hv (x : X) : (a : E) / b x ∈ continuousIntegers ℓ E := by
    change ‖(a : E) / b x‖₊ ≤ 1
    rw [← NNReal.coe_le_coe, NNReal.coe_one, coe_nnnorm, norm_div, hb x]
    exact (div_le_one (norm_pos_iff.mpr ha')).2 le_rfl
  let u : C(X, continuousIntegers ℓ E) :=
    ⟨fun x ↦ ⟨(b x : E) / a, hu x⟩,
      ((continuous_subtype_val.comp b.continuous).div_const (a : E)).subtype_mk _⟩
  let v : C(X, continuousIntegers ℓ E) :=
    ⟨fun x ↦ ⟨(a : E) / b x, hv x⟩,
      (continuous_const.div (continuous_subtype_val.comp b.continuous) hb').subtype_mk _⟩
  let f := continuousMultiplier X (continuousIntegers ℓ E) u
  let g := continuousMultiplier X (continuousIntegers ℓ E) v
  have hfg : f ≫ g = 𝟙 _ := by
    apply regularCoefficient_injective X (continuousIntegers ℓ E)
    rw [regularCoefficient_comp, regularCoefficient_multiplier,
      regularCoefficient_multiplier, regularCoefficient_id]
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    change ((b x : E) / a) * ((a : E) / b x) = 1
    field_simp [hb' x]
  have hgf : g ≫ f = 𝟙 _ := by
    apply regularCoefficient_injective X (continuousIntegers ℓ E)
    rw [regularCoefficient_comp, regularCoefficient_multiplier,
      regularCoefficient_multiplier, regularCoefficient_id]
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    change ((a : E) / b x) * ((b x : E) / a) = 1
    field_simp [hb' x]
  let e : Mod.regular (continuousAbRing X (continuousIntegers ℓ E)) ≅ _ :=
    ⟨f, g, hfg, hgf⟩
  refine ⟨cokernel.mapIso (continuousMultiplier X _ b)
    (continuousMultiplier X _ (ContinuousMap.const X a)) e (Iso.refl _) ?_⟩
  change continuousMultiplier X _ b ≫ 𝟙 _ =
    f ≫ continuousMultiplier X _ (ContinuousMap.const X a)
  rw [Category.comp_id]
  apply regularCoefficient_injective X (continuousIntegers ℓ E)
  rw [regularCoefficient_multiplier, regularCoefficient_comp,
    regularCoefficient_multiplier, regularCoefficient_multiplier]
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  change (b x : E) = ((b x : E) / a) * a
  exact (div_mul_cancel₀ _ ha').symm

private lemma integralConstantNormCokernelSetConstant (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] (X : Scheme.{u})
    (b : C(X, continuousIntegers ℓ E)) (a : continuousIntegers ℓ E) (ha : a ≠ 0)
    (hb : ∀ x, ‖(b x : E)‖ = ‖(a : E)‖) :
    ∃ n : ℕ, Nonempty
      ((Mod.forget (continuousAbRing X (continuousIntegers ℓ E)) ⋙
          sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).obj
        (cokernel (continuousMultiplier X _ b)) ≅
      (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj
        (ULift.{u + 1} (Fin n))) := by
  obtain ⟨e⟩ := integralConstantNormCokernelIso ℓ E X b a ha hb
  obtain ⟨n, ⟨e'⟩⟩ := integralPrincipalCokernelSetConstant ℓ E X a ha
  exact ⟨n, ⟨(Mod.forget _ ⋙
    sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).mapIso e ≪≫ e'⟩⟩

-- A constant positive pivot norm supplies one bound for all its torsion sections.
private lemma integralConstantNormCokernelBound (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (X : Scheme.{u}) (b : C(X, continuousIntegers ℓ E))
    (a : continuousIntegers ℓ E) (ha : a ≠ 0)
    (hb : ∀ x, ‖(b x : E)‖ = ‖(a : E)‖) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (ℓ ^ n) • 𝟙 (cokernel (continuousMultiplier X _ b)) = 0 := by
  have ha' : (a : E) ≠ 0 := fun h ↦ ha (Subtype.ext h)
  have hb' (x : X) : (b x : E) ≠ 0 := by
    intro h
    have he := hb x
    rw [h, norm_zero] at he
    exact ha' (norm_eq_zero.mp he.symm)
  have hnorm : ‖(ℓ : E)‖ < 1 := by
    have he : ‖(ℓ : E)‖ = ‖(ℓ : ℚ_[ℓ])‖ := by
      simpa only [map_natCast] using norm_algebraMap' E (ℓ : ℚ_[ℓ])
    rw [he]
    exact Padic.norm_p_lt_one
  have ht : Filter.Tendsto (fun n : ℕ ↦ ‖(ℓ : E)‖ ^ n)
      Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hnorm
  have hev : ∀ᶠ n : ℕ in Filter.atTop, ‖(ℓ : E)‖ ^ n < ‖(a : E)‖ :=
    (tendsto_order.mp ht).2 _ (norm_pos_iff.mpr ha')
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
  refine ⟨N, fun n hn ↦ ?_⟩
  have hg (x : X) : (ℓ : E) ^ n / b x ∈ continuousIntegers ℓ E := by
    change ‖(ℓ : E) ^ n / b x‖₊ ≤ 1
    rw [← NNReal.coe_le_coe, NNReal.coe_one, coe_nnnorm, norm_div, norm_pow, hb x]
    exact (div_le_one (norm_pos_iff.mpr ha')).2 (hN n hn).le
  let g : C(X, continuousIntegers ℓ E) :=
    ⟨fun x ↦ ⟨(ℓ : E) ^ n / b x, hg x⟩,
      (continuous_const.div (continuous_subtype_val.comp b.continuous) hb').subtype_mk _⟩
  let p := continuousMultiplier X (continuousIntegers ℓ E) b
  let q := continuousMultiplier X (continuousIntegers ℓ E) g
  have hqp : q ≫ p = (ℓ ^ n) • 𝟙 _ := by
    apply regularCoefficient_injective X (continuousIntegers ℓ E)
    rw [regularCoefficient_comp, regularCoefficient_multiplier, regularCoefficient_multiplier]
    apply ContinuousMap.ext
    intro x
    apply Subtype.ext
    change ((ℓ : E) ^ n / b x) * b x = ↑((ℓ ^ n) • (1 : continuousIntegers ℓ E))
    rw [div_mul_cancel₀ _ (hb' x)]
    simp only [nsmul_eq_mul, mul_one]
    norm_cast
  change (ℓ ^ n) • 𝟙 (cokernel p) = 0
  apply (cancel_epi (cokernel.π p)).mp
  have h := hqp =≫ cokernel.π p
  simpa only [Category.assoc, cokernel.condition, Limits.comp_zero,
    Preadditive.nsmul_comp, Category.id_comp, Preadditive.comp_nsmul,
    Category.comp_id] using h.symm

-- The rank-one nonzero case of the local torsion-chart calculation is complete.
private lemma integralCyclicLocalChart (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] (X : Scheme.{u})
    (b : C(X, continuousIntegers ℓ E)) (x : X) (hx : b x ≠ 0) :
    ∃ U : X.Opens, x ∈ U ∧
      let bU := b.comp ⟨U.ι, U.ι.continuous⟩
      (∃ k : ℕ, Nonempty
        ((Mod.forget (continuousAbRing U (continuousIntegers ℓ E)) ⋙
            sheafCompose (Scheme.ProEt.topology U) (forget Ab.{u + 1})).obj
          (cokernel (continuousMultiplier U _ bU)) ≅
        (constantSheaf (Scheme.ProEt.topology U) (Type (u + 1))).obj
          (ULift.{u + 1} (Fin k)))) ∧
      (∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        (ℓ ^ n) • 𝟙 (cokernel (continuousMultiplier U _ bU)) = 0) := by
  let f : C(X, E) := ⟨fun y ↦ (b y : E), continuous_subtype_val.comp b.continuous⟩
  have hx' : f x ≠ 0 := fun h ↦ hx (Subtype.ext h)
  obtain ⟨V, hxU, hU⟩ := constantNormNeighborhood ℓ E X f x hx'
  let U : X.Opens := V
  refine ⟨U, hxU, ?_⟩
  let bU := b.comp ⟨U.ι, U.ι.continuous⟩
  have hb : ∀ y : U, ‖(bU y : E)‖ = ‖(b x : E)‖ :=
    fun y ↦ hU y.val y.property
  exact ⟨integralConstantNormCokernelSetConstant ℓ E U bU (b x) hx hb,
    integralConstantNormCokernelBound ℓ E U bU (b x) hx hb⟩

private lemma finiteConstantAbSet (X : Scheme.{u}) (G : Ab.{u + 1}) [Finite G] :
    ∃ n : ℕ, Nonempty
      ((sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).obj
        ((constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).obj G) ≅
      (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj
        (ULift.{u + 1} (Fin n))) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let e : G ≃ ULift.{u + 1} (Fin (Fintype.card G)) :=
    (Fintype.equivFin G).trans Equiv.ulift.symm
  exact ⟨Fintype.card G, ⟨
    (constantCommuteCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).app G ≪≫
    (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).mapIso e.toIso⟩⟩

private lemma integralFiniteFreeQuotientSetConstant (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] (X : Scheme.{u}) (r k : ℕ)
    (hk : (k : continuousIntegers ℓ E) ≠ 0) :
    ∃ n : ℕ, Nonempty
      ((Mod.forget (continuousAbRing X (continuousIntegers ℓ E)) ⋙
          sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).obj
        (cokernel (k • 𝟙 (Mod.finiteFree
          (continuousAbRing X (continuousIntegers ℓ E)) r))) ≅
      (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj
        (ULift.{u + 1} (Fin n))) := by
  classical
  let R := continuousAbRing X (continuousIntegers ℓ E)
  let Q := (continuousIntegers ℓ E) ⧸ Ideal.span {(k : continuousIntegers ℓ E)}
  let J := Scheme.ProEt.topology X
  let F : Mod (Sheaf J Ab.{u + 1}) R ⥤ Sheaf J Ab.{u + 1} := Mod.forget R
  let M := Mod.finiteFree R r
  let p := continuousMultiplier X (continuousIntegers ℓ E)
    (ContinuousMap.const X (k : continuousIntegers ℓ E))
  have hp : p = k • 𝟙 (Mod.regular R) := by
    apply regularCoefficient_injective X (continuousIntegers ℓ E)
    rw [regularCoefficient_multiplier]
    apply ContinuousMap.ext
    intro x
    change (k : continuousIntegers ℓ E) = k • (1 : continuousIntegers ℓ E)
    simp only [nsmul_eq_mul, mul_one]
  have hm : k • 𝟙 M = biproduct.map (fun _ : Fin r ↦ p) := by
    change k • 𝟙 (⨁ fun _ : Fin r ↦ Mod.regular R) = _
    apply biproduct.hom_ext'
    intro i
    simp only [biproduct.ι_map, hp, Preadditive.comp_nsmul, Category.comp_id,
      Preadditive.nsmul_comp, Category.id_comp]
    rfl
  obtain ⟨eQ⟩ := integralPrincipalCokernelIso ℓ E X (k : continuousIntegers ℓ E) hk
  let eC : F.obj (cokernel (k • 𝟙 M)) ≅ ⨁ fun _ : Fin r ↦ continuousAbRing X Q :=
    F.mapIso (cokernelIsoOfEq hm ≪≫
      finiteDiagonalCokernelIso _ _ (fun _ : Fin r ↦ p)) ≪≫
    F.mapBiproduct (fun _ : Fin r ↦ cokernel p) ≪≫ biproduct.mapIso (fun _ ↦ eQ)
  let : DiscreteTopology Q := integralPrincipalQuotientDiscrete ℓ E _ hk
  let : Finite Q := integralPrincipalQuotientFinite ℓ E _ hk
  obtain ⟨e, he⟩ := Profinite.finiteDiscreteCondensedRing_constant.{u} Q
  obtain ⟨eX, _⟩ := finiteDiscreteSchemeRing_constant Q X e he
  let eAb : (constantSheaf J Ab.{u + 1}).obj (AddCommGrpCat.of (ULift.{u + 1} Q)) ≅
      continuousAbRing X Q := eX ≪≫ asIso (chartComparison X Q)
  let G := ⨁ fun _ : Fin r ↦ AddCommGrpCat.of (ULift.{u + 1} Q)
  let eG : (forget Ab.{u + 1}).obj G ≅ (Fin r → ULift.{u + 1} Q) :=
    (forget Ab.{u + 1}).mapIso (biproduct.isoProduct _) ≪≫
    PreservesProduct.iso (forget Ab.{u + 1}) _ ≪≫ Types.productIso _
  let : Finite G := Finite.of_equiv (Fin r → ULift.{u + 1} Q) eG.toEquiv.symm
  let eB : (constantSheaf J Ab.{u + 1}).obj G ≅
      ⨁ fun _ : Fin r ↦ continuousAbRing X Q :=
    (constantSheaf J Ab.{u + 1}).mapBiproduct _ ≪≫ biproduct.mapIso (fun _ ↦ eAb)
  obtain ⟨n, ⟨en⟩⟩ := finiteConstantAbSet X G
  exact ⟨n, ⟨(sheafCompose J (forget Ab.{u + 1})).mapIso (eC ≪≫ eB.symm) ≪≫ en⟩⟩


private lemma integralColumnDivides (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] (X : Scheme.{u}) (r : ℕ)
    (p : Mod.regular (continuousAbRing X (continuousIntegers ℓ E)) ⟶
      Mod.regular (continuousAbRing X (continuousIntegers ℓ E)))
    (c : Mod.regular (continuousAbRing X (continuousIntegers ℓ E)) ⟶
      Mod.finiteFree (continuousAbRing X (continuousIntegers ℓ E)) r)
    (hp : ∀ x, (regularCoefficient X (continuousIntegers ℓ E) p x).val ≠ 0)
    (hc : ∀ (i : Fin r) x,
      ‖(regularCoefficient X (continuousIntegers ℓ E) (c ≫ biproduct.π _ i) x).val‖ ≤
        ‖(regularCoefficient X (continuousIntegers ℓ E) p x).val‖) :
    ∃ s, p ≫ s = c := by
  classical
  choose q hq using fun i : Fin r ↦
    continuousIntegral_divides ℓ E X p (c ≫ biproduct.π _ i) hp (hc i)
  refine ⟨biproduct.lift q, ?_⟩
  apply biproduct.hom_ext
  intro i
  rw [Category.assoc, biproduct.lift_π]
  have he : p ≫ q i = q i ≫ p := by
    apply regularCoefficient_injective X (continuousIntegers ℓ E)
    rw [regularCoefficient_comp, regularCoefficient_comp]
    exact mul_comm _ _
  rw [he, hq]

private lemma finiteSetBiprod (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (hM : ∃ m : ℕ, Nonempty
      ((Mod.forget R ⋙ sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).obj M ≅
        (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj
          (ULift.{u + 1} (Fin m))))
    (hN : ∃ n : ℕ, Nonempty
      ((Mod.forget R ⋙ sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).obj N ≅
        (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj
          (ULift.{u + 1} (Fin n)))) :
    ∃ k : ℕ, Nonempty
      ((Mod.forget R ⋙ sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).obj
          (M ⊞ N) ≅
        (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj
          (ULift.{u + 1} (Fin k))) := by
  classical
  obtain ⟨m, ⟨em⟩⟩ := hM
  obtain ⟨n, ⟨en⟩⟩ := hN
  let F := Mod.forget R ⋙ sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})
  let K := constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))
  have : F.IsRightAdjoint := ⟨_, ⟨
    (Sheaf.adjunction (Scheme.ProEt.topology X) AddCommGrpCat.adj.{u + 1}).comp
      (Mod.freeForgetAdjunction R)⟩⟩
  have : PreservesFiniteLimits K := by
    dsimp only [K, constantSheaf]
    infer_instance
  let A := ULift.{u + 1} (Fin m)
  let B := ULift.{u + 1} (Fin n)
  let e : A × B ≃ ULift.{u + 1} (Fin (Fintype.card (A × B))) :=
    (Fintype.equivFin (A × B)).trans Equiv.ulift.symm
  refine ⟨Fintype.card (A × B), ⟨F.mapIso (biprod.isoProd M N) ≪≫
    PreservesLimitPair.iso F M N ≪≫ prod.mapIso em en ≪≫
    (PreservesLimitPair.iso K A B).symm ≪≫
    K.mapIso (Types.binaryProductIso A B) ≪≫ K.mapIso e.toIso⟩⟩
private lemma finiteSetBiproduct (X : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R]
    (r : ℕ) (M : Fin r → Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R)
    (hM : ∀ i, ∃ n : ℕ, Nonempty
      ((Mod.forget R ⋙ sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).obj
          (M i) ≅ (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj
            (ULift.{u + 1} (Fin n)))) :
    ∃ k : ℕ, Nonempty
      ((Mod.forget R ⋙ sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).obj
          (⨁ M) ≅ (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj
            (ULift.{u + 1} (Fin k))) := by
  classical
  choose n e using hM
  let F := Mod.forget R ⋙ sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})
  let K := constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))
  have : F.IsRightAdjoint := ⟨_, ⟨
    (Sheaf.adjunction (Scheme.ProEt.topology X) AddCommGrpCat.adj.{u + 1}).comp
      (Mod.freeForgetAdjunction R)⟩⟩
  have : PreservesFiniteLimits K := by
    dsimp only [K, constantSheaf]
    infer_instance
  let A (i : Fin r) := ULift.{u + 1} (Fin (n i))
  let eFin : (∀ i, A i) ≃ ULift.{u + 1} (Fin (Fintype.card (∀ i, A i))) :=
    (Fintype.equivFin (∀ i, A i)).trans Equiv.ulift.symm
  refine ⟨Fintype.card (∀ i, A i), ⟨F.mapIso (biproduct.isoProduct M) ≪≫
    PreservesProduct.iso F M ≪≫ Pi.mapIso (fun i ↦ (e i).some) ≪≫
    (PreservesProduct.iso K A).symm ≪≫ K.mapIso (Types.productIso A) ≪≫
      K.mapIso eFin.toIso⟩⟩

private lemma scalarFiniteFreeMono (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    (X : Scheme.{u}) (r k : ℕ) (hk : (k : continuousIntegers ℓ E) ≠ 0) :
    Mono (k • 𝟙 (Mod.finiteFree (continuousAbRing X (continuousIntegers ℓ E)) r)) := by
  let R := continuousAbRing X (continuousIntegers ℓ E)
  let p := continuousMultiplier X (continuousIntegers ℓ E)
    (ContinuousMap.const X (k : continuousIntegers ℓ E))
  have hp : p = k • 𝟙 (Mod.regular R) := by
    apply regularCoefficient_injective X (continuousIntegers ℓ E)
    rw [regularCoefficient_multiplier]
    apply ContinuousMap.ext
    intro x
    change (k : continuousIntegers ℓ E) = k • (1 : continuousIntegers ℓ E)
    simp only [nsmul_eq_mul, mul_one]
  have : Mono p := continuousRegular_mono X (continuousIntegers ℓ E) p (by
    intro x
    simpa only [p, regularCoefficient_multiplier, ContinuousMap.const_apply] using hk)
  have he : k • 𝟙 (Mod.finiteFree R r) = biproduct.map (fun _ : Fin r ↦ p) := by
    change k • 𝟙 (⨁ fun _ : Fin r ↦ Mod.regular R) = _
    apply biproduct.hom_ext'
    intro i
    simp only [biproduct.ι_map, hp, Preadditive.comp_nsmul, Category.comp_id,
      Preadditive.nsmul_comp, Category.id_comp]
    rfl
  rw [he]
  infer_instance

private lemma integralFreeTorsionScalarChart (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] (X : Scheme.{u}) (r k : ℕ)
    (hk : (k : continuousIntegers ℓ E) ≠ 0)
    (T : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (continuousAbRing X (continuousIntegers ℓ E)))
    (hT : k • 𝟙 T = 0)
    (hTC : ∃ n : ℕ, Nonempty
      ((Mod.forget (continuousAbRing X (continuousIntegers ℓ E)) ⋙
          sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).obj T ≅
        (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj
          (ULift.{u + 1} (Fin n)))) :
    let R := continuousAbRing X (continuousIntegers ℓ E)
    let M := Mod.finiteFree R r
    Mod.IsFree R (image (k • 𝟙 (M ⊞ T))) ∧
    ∃ n : ℕ, Nonempty
      ((Mod.forget R ⋙ sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).obj
          (cokernel (k • 𝟙 (M ⊞ T))) ≅
        (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj
          (ULift.{u + 1} (Fin n))) := by
  let R := continuousAbRing X (continuousIntegers ℓ E)
  let M := Mod.finiteFree R r
  have : Mono (k • 𝟙 M) := scalarFiniteFreeMono ℓ E X r k hk
  have hfree : Mod.IsFree R M := ⟨r, ⟨Iso.refl _⟩⟩
  refine ⟨free_of_iso hfree (scalarImageBiprodIso k M T hT).symm, ?_⟩
  obtain ⟨n, ⟨en⟩⟩ := finiteSetBiprod X R (cokernel (k • 𝟙 M)) T
    (integralFiniteFreeQuotientSetConstant ℓ E X r k hk) hTC
  exact ⟨n, ⟨(Mod.forget R ⋙
    sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).mapIso
      (scalarCokernelBiprodIso k M T hT) ≪≫ en⟩⟩

private lemma integralCyclicBiproductChart (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] (X : Scheme.{u}) (t : ℕ)
    (b : Fin t → C(X, continuousIntegers ℓ E)) (a : Fin t → continuousIntegers ℓ E)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i x, ‖(b i x : E)‖ = ‖(a i : E)‖) :
    let R := continuousAbRing X (continuousIntegers ℓ E)
    let T := ⨁ fun i ↦ cokernel (continuousMultiplier X (continuousIntegers ℓ E) (b i))
    (∃ N : ℕ, ∀ n : ℕ, N ≤ n → (ℓ ^ n) • 𝟙 T = 0) ∧
    ∃ k : ℕ, Nonempty
      ((Mod.forget R ⋙ sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).obj T ≅
        (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj
          (ULift.{u + 1} (Fin k))) := by
  let R := continuousAbRing X (continuousIntegers ℓ E)
  let M (i : Fin t) := cokernel (continuousMultiplier X (continuousIntegers ℓ E) (b i))
  exact ⟨scalarBoundFiniteBiproduct t M (fun n ↦ ℓ ^ n)
      (fun i ↦ integralConstantNormCokernelBound ℓ E X (b i) (a i) (ha i) (hb i)),
    finiteSetBiproduct X R t M
      (fun i ↦ integralConstantNormCokernelSetConstant ℓ E X (b i) (a i) (ha i) (hb i))⟩

private lemma integralDiagonalLocalChart (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E] (X : Scheme.{u}) (r t : ℕ)
    (b : Fin t → C(X, continuousIntegers ℓ E)) (a : Fin t → continuousIntegers ℓ E)
    (ha : ∀ i, a i ≠ 0) (hb : ∀ i x, ‖(b i x : E)‖ = ‖(a i : E)‖) :
    let R := continuousAbRing X (continuousIntegers ℓ E)
    let T := ⨁ fun i ↦ cokernel (continuousMultiplier X (continuousIntegers ℓ E) (b i))
    let P := Mod.finiteFree R r ⊞ T
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      Mod.IsFree R (image ((ℓ ^ n) • 𝟙 P)) ∧
      ∃ k : ℕ, Nonempty
        ((Mod.forget R ⋙ sheafCompose (Scheme.ProEt.topology X) (forget Ab.{u + 1})).obj
            (cokernel ((ℓ ^ n) • 𝟙 P)) ≅
          (constantSheaf (Scheme.ProEt.topology X) (Type (u + 1))).obj
            (ULift.{u + 1} (Fin k))) := by
  obtain ⟨⟨N, hN⟩, hT⟩ := integralCyclicBiproductChart ℓ E X t b a ha hb
  refine ⟨N, fun n hn ↦ ?_⟩
  have hp : (ℓ : ℚ_[ℓ]) ≠ 0 := by
    exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  have hpE : (ℓ : E) ≠ 0 := by
    simpa only [map_natCast, map_zero] using (algebraMap ℚ_[ℓ] E).injective.ne hp
  have hk : ((ℓ ^ n : ℕ) : continuousIntegers ℓ E) ≠ 0 := by
    intro h
    have he := congrArg (continuousIntegers ℓ E).subtype h
    simp only [map_zero, Nat.cast_pow] at he
    exact pow_ne_zero n hpE he
  exact integralFreeTorsionScalarChart ℓ E X r (ℓ ^ n) hk _ (hN n hn) hT

-- Rationalization already has free charts. Keep this proved universe comparison beside
-- the remaining local integral chart construction, for use in its matrix induction.
private lemma resolutionRationalLF (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]
    [FiniteDimensional ℚ_[ℓ] E]
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff ℓ E) X))
    (hP : IsLocallyFinitelyPresented (condensedRingObj (integralCoeff ℓ E) X) P) :
    (∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
      Mod.IsFree ((ProEtale.upperStar Ab.{u + 1} (C.f s)).obj
        (condensedRingObj (Profinite.continuousMapRingObj E) X))
        (((ProEtale.upperStar Ab.{u + 1} (C.f s)).mapMod _).obj
          ((Mod.extendScalars (coefficientMap (integralScalarMap ℓ E) X)).obj P))) := by
  let R := condensedRingObj (integralCoeff ℓ E) X
  let S := condensedRingObj (Profinite.continuousMapRingObj E) X
  let φ := coefficientMap (integralScalarMap ℓ E) X
  let P_E := (Mod.extendScalars φ).obj P
  have hPE : IsLocallyFinitelyPresented S P_E := lfp_extend R S φ hP
  let ψ := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso (liftCoefficientIso E)
  have : IsMonHom ψ.hom := Sheaf.isMonHom_sheafCompose_map _ (liftCoefficientIso E).hom
  let ψX := (upperStarFromPoint X).map ψ.hom
  let E' := ULift.{u} E
  let : NormedField E' :=
    { (inferInstance : NormedCommRing E'), (inferInstance : Field E') with
      norm_mul a b := norm_mul a.down b.down }
  have : IsCommMonObj (Profinite.continuousCoefficientRingObj E') :=
    Sheaf.isCommMonObj_sheafCompose_obj
      (coherentTopology Profinite.{u}) (Profinite.continuousCoefficientRingSheaf E')
      (by
        intro T a b
        apply ULift.ext
        change (a.down * b.down : C(T.unop, E')) = b.down * a.down
        exact mul_comm a.down b.down)
  have h := exists_finiteFree_cover_of_condensedField_lfp ℓ E' X
    ((Mod.comap (inv ψX)).obj P_E) (lfp_comap (inv ψX) hPE)
  exact locally_free_of_iso (locally_free_comap ψX h)
    ((Mod.comapEquivalenceOfIsIso ψX).counitIso.app P_E)

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale

/-- An integral finite-presentation cover admits local torsion bounds and finite quotient charts.

Source: Bhatt--Scholze, Definition 6.8.10, Proposition 6.8.11(3), and the
continuous Smith invariant argument in the parent integral resolution node.
(blueprint: lem-weil-pbc-integral-lfp-local-torsion-charts)

Proof: take local finite presentations and extend scalars to E. The field local
triviality theorem makes the rational cokernel locally finite free. Refine this
cover and use the continuous coefficient realization. Geometric-field evaluation
identifies the pointwise matrix rank with target rank minus rational cokernel rank.
Thus zero-rank pieces have zero matrix; on every other piece choose a maximal-norm
entry and shrink so its norm is constant and dominates every other entry. Divide
by this nowhere-zero entry and perform elementary row and column operations.
Repeat on the smaller matrix. For the finite list of nonzero diagonal functions,
shrink again so each has constant norm. Each such function differs from its
nonzero value at a chosen point by a continuous unit: divide the function and its
point value in both directions, using equality of norms. Its cokernel is therefore
the constant finite principal quotient for that point value. Powers of ℓ tend to
zero, so division by the pivot gives a uniform bound killing this cyclic summand.
These rank-one comparisons and bounds are proved above, as are column division,
block elimination, finite diagonal cokernels, and finite sums of the cyclic charts.
The theorem integralDiagonalLocalChart above supplies the scalar image and finite
quotient conclusions for any such diagonalized presentation, by combining the
cyclic summands and taking the maximum of their bounds. For every n ≥ N, the
image of ℓ^n is the scalar multiple of the
free summand, hence finite free. The quotient is a fixed finite module over
O_E/(ℓ^n), whose discrete topology and finiteness follow from compactness of O_E
and openness of the nonzero principal ideal. Its underlying sheaf of sets is
therefore constant and finite. The construction is local and makes no global
choice of the bound; quasi-compact refinement in the parent theorem supplies that
choice. Zero matrices, zero ranks and empty cover members are included. No data
is chosen from a mere existence theorem in a definition.
-/
theorem integral_lfp_local_torsion_charts
    (X : Scheme.{u}) [TopologicalSpace.NoetherianSpace X]
    (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (CondensedRing.integralCoeff ℓ E) X))
    (hP : IsLocallyFinitelyPresented
      (condensedRingObj (CondensedRing.integralCoeff ℓ E) X) P) :
    ∃ C : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ s : C.I₀,
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        Mod.IsFree ((upperStar Ab.{u + 1} (C.f s)).obj
          (condensedRingObj (CondensedRing.integralCoeff ℓ E) X))
          (((upperStar Ab.{u + 1} (C.f s)).mapMod _).obj
            (image ((ℓ ^ n) • 𝟙 P))) ∧
        ∃ k : ℕ, Nonempty
          ((Scheme.proEtaleSheafInverseImage (C.f s) (Type (u + 1))).obj
            ((Mod.forget _ ⋙ sheafCompose (Scheme.ProEt.topology X)
              (forget Ab.{u + 1})).obj (cokernel ((ℓ ^ n) • 𝟙 P))) ≅
            (constantSheaf (Scheme.ProEt.topology (C.X s)) (Type (u + 1))).obj
              (ULift.{u + 1} (Fin k))) := by sorry

end AlgebraicGeometry.ProEtale
