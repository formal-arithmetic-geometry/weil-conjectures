/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Rational.RationalVerdier
public import WeilConjectures.SixFunctors.Completed.CompletedTensorHomTranspose
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.SitePerfectComplex

import WeilConjectures.SmoothPurity.Integral.IntegralBraidingScalarExtensionSquare
import WeilConjectures.SixFunctors.Rational.RationalHomScalarLocalizedEvaluation

/-! # Canonical rational evaluation comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] WeilConjectures.rationalDerivedTensor
  WeilConjectures.rationalDerivedInternalHom WeilConjectures.podRationalClosed
  WeilConjectures.rationalHomScalarComparison

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  RationalVerdier.units

private theorem scalarMap_integral
    (l : ℕ) [Fact l.Prime] (E F : Type u) [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F) (X : Scheme.{u})
    (A B : sfRationalConstructibleCategory l E X)
    (A₀ B₀ : sfIntegralConstructibleCategory l E X)
    (hA : A = (sfRationalConstructibleLocalization l E X).obj A₀)
    (hB : B = (sfRationalConstructibleLocalization l E X).obj B₀)
    (f : A ⟶ B) (f₀ : A₀ ⟶ B₀)
    (hf : HEq f ((sfRationalConstructibleLocalization l E X).map f₀)) :
    HEq ((RationalVerdier.scalar l X E F ι).map f)
      ((sfRationalConstructibleLocalization l F X).map
        ((RationalVerdier.integralScalar l X E F ι).map f₀)) := by
  cases hA
  cases hB
  cases hf
  simpa only [map_one, sfRationalConstructibleLocalization, ScalarLocalization.localization,
    RationalVerdier.scalar, RationalVerdier.integralScalar] using
    sfRationalScalarExtension_map_tmul l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι A₀ B₀ f₀ 1

private theorem scalarBraiding_hom
    (l : ℕ) [Fact l.Prime] (E F : Type u) [Field E] [Field F]
    [Algebra (Padic l) E] [Algebra (Padic l) F]
    [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F) (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (K L : sfRationalConstructibleCategory l E X) :
    (RationalVerdier.scalar l X E F ι).map
        (pullbackTensorRationalBraiding l E X K L).hom ≫
        (rationalTensorScalarComparison l E F ι X).hom.app (L, K) =
      (rationalTensorScalarComparison l E F ι X).hom.app (K, L) ≫
        (pullbackTensorRationalBraiding l F X
          ((RationalVerdier.scalar l X E F ι).obj K)
          ((RationalVerdier.scalar l X E F ι).obj L)).hom := by
  let S := RationalVerdier.integralScalar l X E F ι
  let G := RationalVerdier.scalar l X E F ι
  let Q := sfRationalConstructibleLocalization l F X
  let TE := rationalDerivedTensor l E X
  let TF := rationalDerivedTensor l F X
  let TI := constructibleIntegralTensor l E X
  let TJ := constructibleIntegralTensor l F X
  have hs (M : sfRationalConstructibleCategory l E X) :
      G.obj M = Q.obj (S.obj M.obj) :=
    sfRationalScalarExtension_obj l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι M
  have ht (M N : sfRationalConstructibleCategory l E X) :
      TE.obj (M, N) = (sfRationalConstructibleLocalization l E X).obj
        (TI.obj (M.obj, N.obj)) :=
    by simpa only [TE, TI, rationalDerivedTensor, sfRationalConstructibleLocalization,
      ScalarLocalization.localization] using
      (rationalDerivedTensor_existsUnique l E X).exists.choose_spec.1 (M, N)
  have hu (M N : sfRationalConstructibleCategory l E X) :
      G.obj (TE.obj (M, N)) = Q.obj (S.obj (TI.obj (M.obj, N.obj))) := by
    rw [hs, ht]
    rfl
  have hv (M N : sfRationalConstructibleCategory l E X) :
      TF.obj (G.obj M, G.obj N) = Q.obj (TJ.obj (S.obj M.obj, S.obj N.obj)) := by
    rw [hs M, hs N]
    simpa only [TF, TJ, rationalDerivedTensor, Q, sfRationalConstructibleLocalization,
      ScalarLocalization.localization] using
      (rationalDerivedTensor_existsUnique l F X).exists.choose_spec.1
        (Q.obj (S.obj M.obj), Q.obj (S.obj N.obj))
  have hb := scalarMap_integral l E F ι X _ _ _ _ (ht K L) (ht L K) _ _
    ((pullbackTensorRationalBraiding_existsUnique l E X K L).exists.choose_spec)
  have hc (M N : sfRationalConstructibleCategory l E X) :=
    (rationalTensorScalarComparison_existsUnique l E F ι X).exists.choose_spec M N
  have hd : HEq (pullbackTensorRationalBraiding l F X (G.obj K) (G.obj L)).hom
      (Q.map (pullbackTensorIntegralBraiding l F X (S.obj K.obj) (S.obj L.obj)).hom) := by
    have h := (pullbackTensorRationalBraiding_existsUnique l F X
      (G.obj K) (G.obj L)).exists.choose_spec
    have hK := congrArg ScalarLocalization.obj (hs K)
    have hL := congrArg ScalarLocalization.obj (hs L)
    exact h.trans (by
      rw [hK, hL]
      rfl)
  apply eq_of_heq
  refine (heq_comp (hu K L) (hu L K) (hv L K) hb (hc L K)).trans ?_
  refine (heq_of_eq ?_).trans
    (heq_comp (hu K L) (hv K L) (hv L K) (hc K L) hd).symm
  rw [← Q.map_comp, ← Q.map_comp]
  exact congrArg Q.map (integralBraidingScalarExtensionSquare l E F ι X K.obj L.obj)

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Finite coefficient passage preserves Hom-first transposition and signed symmetry.
The internal-Hom comparison is the fixed rationalization of the completed one.
Source: blueprint lem-coef-rational-retract-evaluation, proof paragraph 2;
lem-coef-rational-scalar-transpose-compatibility, steps 1--4
(blueprint: lem-coef-rational-hom-scalar-transpose).

Proof: the completed integral Hom comparison is defined by transposing scalar
extension of evaluation. Tensor naturality and the counit identity therefore
identify its composite with the image of every integral transpose. The canonical
completion comparison preserves this identity. Tensor-localize the identity;
both maps are additive and scalar linear, so pure tensors give the equation for
all rational morphisms. For the second equation, on homogeneous representatives
of degrees r,s both paths send (x tensor a) tensor (y tensor b) to
(-1)^(r*s) (y tensor x) tensor (a*b). The fixed quotient comparisons and both
Roos coordinates preserve this equality, as does scalar localization. Nothing
in either calculation requires W to be dualizing, and coefficient embeddings
need not be literal inclusions: the same balanced tensor calculation applies. -/
theorem rationalHomScalar_transpose
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F) :
    (∀ (K L W : sfRationalConstructibleCategory l E X)
      (hL : constructibleRationalHomPairs l E X (op L, W))
      (b : (RationalVerdier.tensor D l hl X E).obj (K, L) ⟶ W),
      (@podRationalClosed l _ F _ _ _ X (RationalVerdier.units D l hl X)).transpose
          ((RationalVerdier.scalar l X E F ι).obj K)
          (rationalHomScalarPair l E F ι X ⟨(op L, W), hL⟩)
          ((@rationalTensorScalarComparison l _ E _ _ _ F _ _ _ ι X
            (RationalVerdier.units D l hl X)).inv.app (K, L) ≫
              (RationalVerdier.scalar l X E F ι).map b) =
        (RationalVerdier.scalar l X E F ι).map
          ((@podRationalClosed l _ E _ _ _ X (RationalVerdier.units D l hl X)).transpose
            K ⟨(op L, W), hL⟩ b) ≫
          (rationalHomScalarComparison l E F ι X ⟨(op L, W), hL⟩).hom) ∧
    (∀ K L : sfRationalConstructibleCategory l E X,
      (@pullbackTensorRationalBraiding l _ F _ _ _ X
        (RationalVerdier.units D l hl X)
        ((RationalVerdier.scalar l X E F ι).obj L)
        ((RationalVerdier.scalar l X E F ι).obj K)).hom ≫
      (@rationalTensorScalarComparison l _ E _ _ _ F _ _ _ ι X
        (RationalVerdier.units D l hl X)).inv.app (K, L) =
      (@rationalTensorScalarComparison l _ E _ _ _ F _ _ _ ι X
        (RationalVerdier.units D l hl X)).inv.app (L, K) ≫
      (RationalVerdier.scalar l X E F ι).map
        ((@pullbackTensorRationalBraiding l _ E _ _ _ X
          (RationalVerdier.units D l hl X) L K).hom)) := by
  constructor
  · intro K L W hL b
    let := RationalVerdier.units D l hl X
    let G := RationalVerdier.scalar l X E F ι
    let TE := rationalDerivedTensor l E X
    let TF := rationalDerivedTensor l F X
    let SE := podRationalClosed l E X
    let SF := podRationalClosed l F X
    let P : (constructibleRationalHomPairs l E X).FullSubcategory :=
      ⟨(op L, W), hL⟩
    let PF := rationalHomScalarPair l E F ι X P
    let H := (rationalDerivedInternalHom l E X).obj P
    let c := (rationalHomScalarComparison l E F ι X P).hom
    let μ := rationalTensorScalarComparison l E F ι X
    have hc : SF.transpose (G.obj H) PF
        (μ.inv.app (H, L) ≫ G.map (SE.evaluation P)) = c := by
      rw [← rationalHomScalar_localizedEvaluation D l hl X E F ι P]
      erw [SF.parameter_naturality]
      change c ≫ SF.transpose _ PF (SF.evaluation PF) = c
      rw [PodPartialClosed.evaluation, AddEquiv.apply_symm_apply, Category.comp_id]
    let t := SE.transpose K P b
    have hev : TE.map (Prod.mkHom t (𝟙 L)) ≫ SE.evaluation P = b := by
      apply (SE.transpose K P).injective
      rw [SE.parameter_naturality]
      simp only [PodPartialClosed.evaluation, AddEquiv.apply_symm_apply,
        Category.comp_id]
      rfl
    have hn : TF.map (Prod.mkHom (G.map t) (𝟙 (G.obj L))) ≫ μ.inv.app (H, L) =
        μ.inv.app (K, L) ≫ G.map (TE.map (Prod.mkHom t (𝟙 L))) := by
      have h := μ.inv.naturality (Prod.mkHom t (𝟙 L))
      change TF.map (Prod.mkHom (G.map t) (G.map (𝟙 L))) ≫ μ.inv.app (H, L) =
        μ.inv.app (K, L) ≫ G.map (TE.map (Prod.mkHom t (𝟙 L))) at h
      rw [G.map_id] at h
      exact h
    change SF.transpose (G.obj K) PF (μ.inv.app (K, L) ≫ G.map b) = G.map t ≫ c
    rw [← hc, ← SF.parameter_naturality]
    congr 1
    rw [← Category.assoc]
    erw [hn]
    rw [Category.assoc, ← G.map_comp, hev]
  · intro K L
    let := RationalVerdier.units D l hl X
    have h := scalarBraiding_hom l E F ι X L K
    apply (Iso.comp_inv_eq
      ((rationalTensorScalarComparison l E F ι X).app (K, L))).2
    symm
    rw [Category.assoc]
    exact (Iso.inv_comp_eq
      ((rationalTensorScalarComparison l E F ι X).app (L, K))).2 h

end WeilConjectures
