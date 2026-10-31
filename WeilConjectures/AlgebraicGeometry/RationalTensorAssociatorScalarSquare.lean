/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorConstraints
import all WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorConstraints
import WeilConjectures.AlgebraicGeometry.IntegralPullbackTensorAssociatorNaturality
import WeilConjectures.AlgebraicGeometry.IntegralTensorAssociatorScalarSquare

/-! # Scalar coherence and naturality of the prescribed rational tensor associator

Source: literature/stacks-project/sites-cohomology.tex, Tag 07A4, label
lemma-pullback-tensor-product; normalized completed/rational associator compatibility
(blueprint: lem-pur-rational-tensor-associator-scalar-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures

namespace WeilConjectures

attribute [local irreducible] Scheme.residueField

open scoped TensorProduct

private theorem chosen_operation_spec {A : Sort*} {p : A → Prop}
    (h : ∃! a, p a) (a : A) (ha : a = h.exists.choose) : p a :=
  ha.symm ▸ h.exists.choose_spec

private theorem tensor_map_heq {C : Type*} [Category* C] (T : C × C ⥤ C)
    {A B D E A' B' D' E' : C}
    (hA : A = A') (hB : B = B') (hD : D = D') (hE : E = E')
    {f : A ⟶ B} {f' : A' ⟶ B'} {g : D ⟶ E} {g' : D' ⟶ E'}
    (hf : HEq f f') (hg : HEq g g') :
    HEq (T.map (Prod.mkHom f g)) (T.map (Prod.mkHom f' g')) := by
  subst A' B' D' E'
  cases hf
  cases hg
  rfl


/-- The prescribed rational tensor associator is natural and commutes with the
specified scalar extension tensor comparison.

Source: literature/stacks-project/sites-cohomology.tex, Tag 07A4, label
lemma-pullback-tensor-product; the naturality clause is the arbitrary-arrow
naturality equation, and the scalar clause is the two composites obtained from
`rationalTensorScalarComparison` (blueprint: lem-pur-rational-tensor-associator-scalar-square).

Proof. Step 1 (integral objects). Choose the normalized primitive scalar model `S_Y`
and normalized Roos models from the ambient comparison-system family, and the tensor
model realizations `T_E, T_L` of the stage3 tensor-model normalization. The
reduction-intertwining lemma makes `γ` the invertible `scalarReduction` comparison of
`S_Y`. The stage3 scalar/tensor limit-square identifies the completed scalar/tensor
comparison with the two `scalarReduction` maps and `derivedSigma`. Apply coherent
reduction, use counit naturality and the derived-limit comparison of the
scalar-extension tower, and cancel `γ`, `γ ⊗ (γ ⊗ γ)` and the tensor reduction
comparison `r`. The system-associator lemma replaces the nested `derivedSigma`
composites by the `systemClosed.monoidal` associator, so both coherent reductions over
`𝒪_L` agree. Fully faithful coherent reduction reflects this, and the uniqueness
defining `pullbackTensorIntegralAssociator` gives the integral square
`B(α^int,E) ; B^⊗,r = B^⊗,l ; α^int,L`. The integral naturality lemma gives
integral naturality for arbitrary derived morphisms.
Step 2 (localization). The rational associator and `b` are the localizations of the
integral associator and of `integralTensorScalarComparison`; raw rationalization
preserves composition, so localizing Step 1 gives both equations on integral arrows.
Step 3 (all rational arrows). A rational morphism is a finite sum of pure integral
morphisms tensored with field scalars; the additive and balanced pure-tensor formulas
of the rational operations and of `sfRationalScalarExtension` extend both equations to
arbitrary `X, Y, Z` and arrows. This includes `E = L` and ramified extensions; no
finite-Tor or finite-type hypothesis is used.
-/
theorem rationalTensorAssociator_scalar_square
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L]
    [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L)
    (W : Scheme.{u}) [∀ w : W, Invertible (l : W.residueField w)] :
    (∀ {K K' M M' N N' : sfRationalConstructibleCategory l E W}
      (f : K ⟶ K') (g : M ⟶ M') (h : N ⟶ N'),
      (rationalDerivedTensor l E W).map
          (Prod.mkHom ((rationalDerivedTensor l E W).map (Prod.mkHom f g)) h) ≫
          (pullbackTensorRationalAssociator l E W K' M' N').hom =
        (pullbackTensorRationalAssociator l E W K M N).hom ≫
          (rationalDerivedTensor l E W).map
            (Prod.mkHom f ((rationalDerivedTensor l E W).map (Prod.mkHom g h)))) ∧
    (∀ (X Y Z : sfRationalConstructibleCategory l E W),
      (sfRationalScalarExtension l E W 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map
          (pullbackTensorRationalAssociator l E W X Y Z).hom ≫
        (rationalTensorScalarComparison l E L ι W).hom.app
          (X, (rationalDerivedTensor l E W).obj (Y, Z)) ≫
        (rationalDerivedTensor l L W).map
          (Prod.mkHom (𝟙 _) ((rationalTensorScalarComparison l E L ι W).hom.app
            (Y, Z))) =
      (rationalTensorScalarComparison l E L ι W).hom.app
          ((rationalDerivedTensor l E W).obj (X, Y), Z) ≫
        (rationalDerivedTensor l L W).map
          (Prod.mkHom ((rationalTensorScalarComparison l E L ι W).hom.app
            (X, Y)) (𝟙 _)) ≫
        (pullbackTensorRationalAssociator l L W
          ((sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj X)
          ((sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj Y)
          ((sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj Z)).hom) := by
  constructor
  · intro K K' M M' N N' f g h
    let F := rationalDerivedTensor l E W
    have spec := chosen_operation_spec (rationalDerivedTensor_existsUnique l E W) F rfl
    let I := constructibleIntegralTensor l E W
    let R := Padic.coefficientExtensionIntegers l E
    let p := Padic.coefficientExtensionUniformizer l E
    have ho (MN : sfRationalConstructibleCategory l E W ×
        sfRationalConstructibleCategory l E W) :
        F.obj MN = ScalarLocalization.mk (I.obj (MN.1.obj, MN.2.obj)) :=
      spec.1 MN
    let b (A A' B B' : sfRationalConstructibleCategory l E W) :
        (A ⟶ A') →ₗ[Localization.Away p] (B ⟶ B') →ₗ[Localization.Away p]
          (F.obj (A, B) ⟶ F.obj (A', B')) :=
      (spec.2 A A' B B').choose
    have hb (A A' B B' : sfRationalConstructibleCategory l E W)
        (f : A ⟶ A') (g : B ⟶ B') : F.map (Prod.mkHom f g) = b A A' B B' f g :=
      (spec.2 A A' B B').choose_spec.1 f g
    have hp (A A' B B' : sfRationalConstructibleCategory l E W)
        (f : A.obj ⟶ A'.obj) (g : B.obj ⟶ B'.obj) (a c : Localization.Away p) :
        HEq (F.map (Prod.mkHom (a ⊗ₜ[R] f) (c ⊗ₜ[R] g)))
          ((a * c) ⊗ₜ[R] I.map (Prod.mkHom f g)) := by
      rw [hb]
      exact (spec.2
        A A' B B').choose_spec.2 f g a c
    have hlobj (A B C : sfRationalConstructibleCategory l E W) :
        F.obj (F.obj (A, B), C) =
          ScalarLocalization.mk (I.obj (I.obj (A.obj, B.obj), C.obj)) := by
      rw [ho, ho]
    have hrobj (A B C : sfRationalConstructibleCategory l E W) :
        F.obj (A, F.obj (B, C)) =
          ScalarLocalization.mk (I.obj (A.obj, I.obj (B.obj, C.obj))) := by
      rw [ho, ho]
    change F.map (Prod.mkHom (F.map (Prod.mkHom f g)) h) ≫
        (pullbackTensorRationalAssociator l E W K' M' N').hom =
      (pullbackTensorRationalAssociator l E W K M N).hom ≫
        F.map (Prod.mkHom f (F.map (Prod.mkHom g h)))
    induction f using TensorProduct.induction_on with
    | zero =>
      simp only [hb, LinearMap.map_zero, LinearMap.zero_apply, Limits.zero_comp,
        Limits.comp_zero]
    | add f f' hf hf' =>
      simpa only [hb, LinearMap.map_add, LinearMap.add_apply, Preadditive.add_comp,
        Preadditive.comp_add] using congrArg₂ (· + ·) hf hf'
    | tmul a f =>
      induction g using TensorProduct.induction_on with
      | zero =>
        simp only [hb, LinearMap.map_zero, LinearMap.zero_apply, Limits.zero_comp,
          Limits.comp_zero]
      | add g g' hg hg' =>
        simpa only [hb, LinearMap.map_add, LinearMap.add_apply, Preadditive.add_comp,
          Preadditive.comp_add] using congrArg₂ (· + ·) hg hg'
      | tmul c g =>
        induction h using TensorProduct.induction_on with
        | zero =>
          simp only [hb, LinearMap.map_zero, Limits.zero_comp, Limits.comp_zero]
        | add h h' hh hh' =>
          simpa only [hb, LinearMap.map_add, LinearMap.add_apply, Preadditive.add_comp,
            Preadditive.comp_add] using congrArg₂ (· + ·) hh hh'
        | tmul d h =>
          have hfg := hp K K' M M' f g a c
          have hgh := hp M M' N N' g h c d
          have hleft := (tensor_map_heq F (ho (K, M)) (ho (K', M')) rfl rfl
            hfg HEq.rfl).trans
              (hp (ScalarLocalization.mk (I.obj (K.obj, M.obj)))
                (ScalarLocalization.mk (I.obj (K'.obj, M'.obj))) N N'
                (I.map (Prod.mkHom f g)) h (a * c) d)
          have hright := (tensor_map_heq F rfl rfl (ho (M, N)) (ho (M', N'))
            HEq.rfl hgh).trans
              (hp K K' (ScalarLocalization.mk (I.obj (M.obj, N.obj)))
                (ScalarLocalization.mk (I.obj (M'.obj, N'.obj)))
                f (I.map (Prod.mkHom g h)) a (c * d))
          have ha := (pullbackTensorRationalAssociator_existsUnique l E W K M N).exists.choose_spec
          have ha' :=
            (pullbackTensorRationalAssociator_existsUnique l E W K' M' N').exists.choose_spec
          have hl := heq_comp (hlobj K M N) (hlobj K' M' N') (hrobj K' M' N') hleft ha'
          have hr := heq_comp (hlobj K M N) (hrobj K M N) (hrobj K' M' N') ha hright
          apply eq_of_heq
          refine hl.trans ((heq_of_eq ?_).trans hr.symm)
          change ScalarLocalization.composition R _ p _ _ _
              (1 ⊗ₜ[R] (pullbackTensorIntegralAssociator l E W K'.obj M'.obj N'.obj).hom)
              (((a * c) * d) ⊗ₜ[R] I.map (Prod.mkHom (I.map (Prod.mkHom f g)) h)) =
            ScalarLocalization.composition R _ p _ _ _
              ((a * (c * d)) ⊗ₜ[R] I.map (Prod.mkHom f (I.map (Prod.mkHom g h))))
              (1 ⊗ₜ[R] (pullbackTensorIntegralAssociator l E W K.obj M.obj N.obj).hom)
          simp only [ScalarLocalization.composition_tmul, one_mul, mul_one, mul_assoc]
          rw [pullbackTensorIntegralAssociator_naturality l E W f g h]
  · intro M N P
    let F := sfRationalScalarExtension l E W 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι
    let I := sfConstructibleIntegralScalarExtension 0 l
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) E L ι W
    let Q := sfRationalConstructibleLocalization l L W
    have hF (K) : F.obj K =
        (sfRationalConstructibleLocalization l L W).obj (I.obj K.obj) :=
      sfRationalScalarExtension_obj l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι K
    have hTY (MN) : (rationalDerivedTensor l E W).obj MN =
        (sfRationalConstructibleLocalization l E W).obj
          ((constructibleIntegralTensor l E W).obj (MN.1.obj,MN.2.obj)) :=
      (rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1 MN
    have hTX (MN) : (rationalDerivedTensor l L W).obj MN =
        Q.obj ((constructibleIntegralTensor l L W).obj (MN.1.obj,MN.2.obj)) :=
      (rationalDerivedTensor_existsUnique l L W).exists.choose_spec.1 MN
    have hmap {A B : sfRationalConstructibleCategory l E W}
        {A' B' : sfIntegralConstructibleCategory l E W}
        (hA : A = (sfRationalConstructibleLocalization l E W).obj A')
        (hB : B = (sfRationalConstructibleLocalization l E W).obj B')
        (a : A ⟶ B) (b : A' ⟶ B')
        (hab : HEq a ((sfRationalConstructibleLocalization l E W).map b)) :
        HEq (F.map a) (Q.map (I.map b)) := by
      exact map_localized_heq I F (sfRationalConstructibleLocalization l E W) Q
        (fun {K K'} c ↦ by
          have hh := sfRationalScalarExtension_map_tmul l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι K K' c 1
          have hQ : HEq (Q.map (I.map c))
              ((1 : Localization.Away (Padic.coefficientExtensionUniformizer l L))
                ⊗ₜ[Padic.coefficientExtensionIntegers l L] I.map c) := by rfl
          simp only [map_one] at hh
          exact hh.trans hQ.symm)
        hA hB a b hab
    have hbase (K) : (F.obj K).obj = I.obj K.obj := by rw [hF]; rfl
    have hty (A B : sfRationalConstructibleCategory l E W) :
        ((rationalDerivedTensor l E W).obj (A,B)).obj =
          (constructibleIntegralTensor l E W).obj (A.obj,B.obj) := by rw [hTY]; rfl
    have htx (A B : sfRationalConstructibleCategory l L W) :
        ((rationalDerivedTensor l L W).obj (A,B)).obj =
          (constructibleIntegralTensor l L W).obj (A.obj,B.obj) := by rw [hTX]; rfl
    have htmap {A B C D : sfRationalConstructibleCategory l L W}
        {A' B' C' D' : sfIntegralConstructibleCategory l L W}
        (hA : A = Q.obj A') (hB : B = Q.obj B')
        (hC : C = Q.obj C') (hD : D = Q.obj D')
        (a : A ⟶ B) (b : C ⟶ D) (a' : A' ⟶ B') (b' : C' ⟶ D')
        (ha : HEq a (Q.map a')) (hb : HEq b (Q.map b')) :
        HEq ((rationalDerivedTensor l L W).map (Prod.mkHom a b))
          (Q.map ((constructibleIntegralTensor l L W).map (Prod.mkHom a' b'))) := by
      subst A B C D
      have ha' := eq_of_heq ha
      have hb' := eq_of_heq hb
      subst a b
      obtain ⟨bil, hbil, hbil'⟩ :=
        (rationalDerivedTensor_existsUnique l L W).exists.choose_spec.2
          (Q.obj A') (Q.obj B') (Q.obj C') (Q.obj D')
      change HEq ((rationalDerivedTensor_existsUnique l L W).exists.choose.map
        (Prod.mkHom (Q.map a') (Q.map b'))) _
      rw [hbil]
      have hQ : HEq
          (Q.map ((constructibleIntegralTensor l L W).map (Prod.mkHom a' b')))
          ((1 : Localization.Away (Padic.coefficientExtensionUniformizer l L))
            ⊗ₜ[Padic.coefficientExtensionIntegers l L]
              (constructibleIntegralTensor l L W).map (Prod.mkHom a' b')) := by rfl
      have hh := hbil' a' b' 1 1
      simp only [one_mul] at hh
      exact hh.trans hQ.symm
    have hc (A B B' : sfIntegralConstructibleCategory l E W) (h : B = B') :
        HEq (Q.map (integralTensorScalarComparison l E L ι W A B).hom)
          (Q.map (integralTensorScalarComparison l E L ι W A B').hom) := by
      subst B'
      rfl
    have ha := (pullbackTensorRationalAssociator_existsUnique l E W M N P).exists.choose_spec
    have ha' := hmap (by rw [hTY, hTY]; rfl) (by rw [hTY, hTY]; rfl) _ _ ha
    have hmid := (rationalTensorScalarComparison_existsUnique l E L ι W).exists.choose_spec M
      ((rationalDerivedTensor l E W).obj (N,P))
    have hmid' : HEq ((rationalTensorScalarComparison l E L ι W).hom.app
        (M, (rationalDerivedTensor l E W).obj (N,P)))
        (Q.map (integralTensorScalarComparison l E L ι W M.obj
          ((constructibleIntegralTensor l E W).obj (N.obj,P.obj))).hom) :=
      hmid.trans (hc M.obj _ _ (hty N P))
    have hnp := (rationalTensorScalarComparison_existsUnique l E L ι W).exists.choose_spec N P
    have hid : HEq (𝟙 (F.obj M)) (Q.map (𝟙 (I.obj M.obj))) := by
      have hh {A : sfRationalConstructibleCategory l L W}
          {B : sfIntegralConstructibleCategory l L W} (h : A = Q.obj B) :
          HEq (𝟙 A) (Q.map (𝟙 B)) := by subst A; simp
      exact hh (hF M)
    have hnp' := htmap (hF M) (hF M) (by
        simp only [Functor.comp_obj]
        rw [hF, hTY]
        rfl)
      (by
        simp only [Functor.comp_obj, Functor.prod_obj]
        rw [hTX, hF, hF]
        rfl) (𝟙 (F.obj M)) _ _ _ hid hnp
    have hleft₁ := heq_comp (by
        rw [hF, hTY, hTY]
        rfl)
      (by
        rw [hF, hTY, hTY]
        rfl) (by
        simp only [Functor.comp_obj, Functor.prod_obj]
        rw [hTX, hF, hF, hTY]
        rfl) ha' hmid'
    have hleft := heq_comp (by
        rw [hF, hTY, hTY]
        rfl)
      (by
        simp only [Functor.comp_obj, Functor.prod_obj]
        rw [hTX, hF, hF, hTY]
        rfl)
      (by
        simp only [Functor.comp_obj, Functor.prod_obj]
        rw [hTX, hTX, hF, hF, hF]
        rfl) hleft₁ hnp'
    have hmn := (rationalTensorScalarComparison_existsUnique l E L ι W).exists.choose_spec M N
    have hrmid := (rationalTensorScalarComparison_existsUnique l E L ι W).exists.choose_spec
      ((rationalDerivedTensor l E W).obj (M,N)) P
    have hc' (A A' B : sfIntegralConstructibleCategory l E W) (h : A = A') :
        HEq (Q.map (integralTensorScalarComparison l E L ι W A B).hom)
          (Q.map (integralTensorScalarComparison l E L ι W A' B).hom) := by
      subst A'
      rfl
    have hrmid' := hrmid.trans (hc' _ _ P.obj (hty M N))
    have hid' : HEq (𝟙 (F.obj P)) (Q.map (𝟙 (I.obj P.obj))) := by
      have hh {A : sfRationalConstructibleCategory l L W}
          {B : sfIntegralConstructibleCategory l L W} (h : A = Q.obj B) :
          HEq (𝟙 A) (Q.map (𝟙 B)) := by subst A; simp
      exact hh (hF P)
    have hmn' := htmap (by
        simp only [Functor.comp_obj]
        rw [hF, hTY]
        rfl)
      (by
        simp only [Functor.comp_obj, Functor.prod_obj]
        rw [hTX, hF, hF]
        rfl) (hF P) (hF P) _ (𝟙 (F.obj P)) _ _ hmn hid'
    have hrassoc := (pullbackTensorRationalAssociator_existsUnique l L W
      (F.obj M) (F.obj N) (F.obj P)).exists.choose_spec
    have has {A B C A' B' C' : sfIntegralConstructibleCategory l L W}
        (hA : A = A') (hB : B = B') (hC : C = C') :
        HEq (Q.map (pullbackTensorIntegralAssociator l L W A B C).hom)
          (Q.map (pullbackTensorIntegralAssociator l L W A' B' C').hom) := by
      subst A' B' C'
      rfl
    have hrassoc' := hrassoc.trans (has (hbase M) (hbase N) (hbase P))
    have hright₁ := heq_comp (by
        simp only [Functor.comp_obj]
        rw [hF, hTY, hTY]
        rfl)
      (by
        simp only [Functor.comp_obj, Functor.prod_obj]
        rw [hTX, hF, hTY, hF]
        rfl)
      (by
        simp only [Functor.comp_obj, Functor.prod_obj]
        rw [hTX, hTX, hF, hF, hF]
        rfl) hrmid' hmn'
    have hright := heq_comp (by
        simp only [Functor.comp_obj]
        rw [hF, hTY, hTY]
        rfl)
      (by
        simp only [Functor.comp_obj, Functor.prod_obj]
        rw [hTX, hTX, hF, hF, hF]
        rfl)
      (by
        rw [hTX, hTX, hF, hF, hF]
        rfl) hright₁ hrassoc'
    simp only [← Category.assoc]
    apply eq_of_heq
    simp only [← Functor.map_comp] at hleft hright
    have hh := integralTensorAssociator_scalar_square l E L ι W M.obj N.obj P.obj
    simp only [← Category.assoc] at hh
    simpa only [pullbackTensorRationalAssociator, rationalTensorScalarComparison, F] using
      hleft.trans ((heq_of_eq (congrArg Q.map hh)).trans hright.symm)

end WeilConjectures
