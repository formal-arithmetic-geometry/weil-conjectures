/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Rational.RationalVerdier
public import WeilConjectures.SixFunctors.Completed.CompletedTensorHomTranspose
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.SitePerfectComplex

import WeilConjectures.SixFunctors.Rational.RationalHomScalarIntegralEvaluation
import all WeilConjectures.SixFunctors.Normalized.NormalizedRationalEvaluationNaturality
import all WeilConjectures.SmoothPurity.Finite.FiniteRationalDerivedOperations

/-! # Localization of the scalar Hom evaluation square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

attribute [local irreducible] WeilConjectures.rationalDerivedTensor
  WeilConjectures.rationalDerivedInternalHom WeilConjectures.podRationalClosed
  WeilConjectures.rationalHomScalarComparison
  WeilConjectures.rationalTensorScalarComparison
  WeilConjectures.integralTensorScalarComparison
  WeilConjectures.integralHomScalarComparison
  WeilConjectures.constructibleIntegralHom WeilConjectures.constructibleIntegralTensor
  WeilConjectures.podIntegralClosed

universe u
open CategoryTheory Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local irreducible] Scheme.residueField HasDerivedCategory.standard
  RationalVerdier.units

private theorem iso_inv_heq {C : Type*} [Category* C] {X Y X' Y' : C}
    (e : X ≅ Y) (e' : X' ≅ Y') (hx : X = X') (hy : Y = Y')
    (h : HEq e.hom e'.hom) : HEq e.inv e'.inv := by
  cases hx
  cases hy
  have he : e = e' := Iso.ext (eq_of_heq h)
  cases he
  rfl

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

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (X : Scheme.{u}) [X.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
omit [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))] in
private theorem scalarEvaluation_left
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F)
    (P : (constructibleRationalHomPairs l E X).FullSubcategory) :
    letI := RationalVerdier.units D l hl X
    let G := RationalVerdier.scalar l X E F ι
    let PI := integralPairOfRationalHomPair l E X P
    let S := RationalVerdier.integralScalar l X E F ι
    let Q := sfRationalConstructibleLocalization l F X
    HEq ((rationalDerivedTensor l F X).map
        (Prod.mkHom (rationalHomScalarComparison l E F ι X P).hom
          (𝟙 (G.obj P.obj.1.unop))) ≫
      (podRationalClosed l F X).evaluation (rationalHomScalarPair l E F ι X P))
      (Q.map ((constructibleIntegralTensor l F X).map
        (Prod.mkHom (integralHomScalarComparison l E F ι X PI).hom
          (𝟙 (S.obj PI.obj.1.unop))) ≫
        (podIntegralClosed l F X).evaluation (integralHomScalarPair l E F ι X PI))) := by
  let := RationalVerdier.units D l hl X
  dsimp only
  let G := RationalVerdier.scalar l X E F ι
  let S := RationalVerdier.integralScalar l X E F ι
  let QE := sfRationalConstructibleLocalization l E X
  let QF := sfRationalConstructibleLocalization l F X
  let PI := integralPairOfRationalHomPair l E X P
  let PF := rationalHomScalarPair l E F ι X P
  let PFI := integralHomScalarPair l E F ι X PI
  let H := (rationalDerivedInternalHom l E X).obj P
  let HI := (constructibleIntegralHom l E X).obj PI
  let HF := (rationalDerivedInternalHom l F X).obj PF
  let HFI := (constructibleIntegralHom l F X).obj PFI
  have hs (M : sfRationalConstructibleCategory l E X) :
      G.obj M = QF.obj (S.obj M.obj) :=
    sfRationalScalarExtension_obj l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι M
  have hH : H = QE.obj HI := by
    simpa only [H, HI, PI, QE, rationalDerivedInternalHom,
      sfRationalConstructibleLocalization, ScalarLocalization.localization] using
      (rationalDerivedInternalHom_existsUnique l E X).exists.choose_spec.1 P
  have hp : integralPairOfRationalHomPair l F X PF = PFI := by
    apply ObjectProperty.FullSubcategory.ext
    change (op ((G.obj P.obj.1.unop).obj), (G.obj P.obj.2).obj) = _
    rw [hs P.obj.1.unop, hs P.obj.2]
    rfl
  have hHF : HF = QF.obj HFI := by
    dsimp only [HF]
    have hh : (rationalDerivedInternalHom l F X).obj PF =
        QF.obj ((constructibleIntegralHom l F X).obj
          (integralPairOfRationalHomPair l F X PF)) := by
      simpa only [rationalDerivedInternalHom, QF, sfRationalConstructibleLocalization,
        ScalarLocalization.localization] using
        (rationalDerivedInternalHom_existsUnique l F X).exists.choose_spec.1 PF
    rw [hh, hp]
  have hGH : G.obj H = QF.obj (S.obj HI) := by rw [hs, hH]; rfl
  have hK : G.obj P.obj.1.unop = QF.obj (S.obj PI.obj.1.unop) := hs _
  have hW : G.obj P.obj.2 = QF.obj (S.obj PI.obj.2) := hs _
  have ht (M N : sfRationalConstructibleCategory l F X) :
      (rationalDerivedTensor l F X).obj (M, N) =
        QF.obj ((constructibleIntegralTensor l F X).obj (M.obj, N.obj)) :=
    by simpa only [rationalDerivedTensor, QF, sfRationalConstructibleLocalization,
      ScalarLocalization.localization] using
      (rationalDerivedTensor_existsUnique l F X).exists.choose_spec.1 (M, N)
  have hsrc : (rationalDerivedTensor l F X).obj (G.obj H, G.obj P.obj.1.unop) =
      QF.obj ((constructibleIntegralTensor l F X).obj
        (S.obj HI, S.obj PI.obj.1.unop)) := by rw [ht, hGH, hK]; rfl
  have hmid : (rationalDerivedTensor l F X).obj (HF, G.obj P.obj.1.unop) =
      QF.obj ((constructibleIntegralTensor l F X).obj (HFI, S.obj PI.obj.1.unop)) := by
    rw [ht, hHF, hK]; rfl
  have hc : HEq (rationalHomScalarComparison l E F ι X P).hom
      (QF.map (integralHomScalarComparison l E F ι X PI).hom) := by
    simpa only [rationalHomScalarComparison] using
      (rationalHomScalarComparison_existsUnique l E F ι X P).exists.choose_spec
  have hid : HEq (𝟙 (G.obj P.obj.1.unop))
      (QF.map (𝟙 (S.obj PI.obj.1.unop))) := by
    rw [hK, QF.map_id]
  have hm := tensorMap_heq _ (constructibleIntegralTensor l F X)
    (rationalDerivedTensor l F X)
    (rationalTensor_spec l F X).2
    hGH hHF hK hK
    (integralHomScalarComparison l E F ι X PI).hom (𝟙 _) 1 1 hc hid
  simp only [one_mul] at hm
  have heF := rationalEvaluation_normalization l F X PF
  rw [hp] at heF
  exact (heq_comp hsrc hmid hW hm heF).trans
    (heq_of_eq (QF.map_comp _ _).symm)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
omit [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
  [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))] in
private theorem scalarEvaluation_right
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F)
    (P : (constructibleRationalHomPairs l E X).FullSubcategory) :
    letI := RationalVerdier.units D l hl X
    let G := RationalVerdier.scalar l X E F ι
    let PI := integralPairOfRationalHomPair l E X P
    let S := RationalVerdier.integralScalar l X E F ι
    let Q := sfRationalConstructibleLocalization l F X
    HEq ((rationalTensorScalarComparison l E F ι X).inv.app
        ((rationalDerivedInternalHom l E X).obj P, P.obj.1.unop) ≫
      G.map ((podRationalClosed l E X).evaluation P))
      (Q.map ((integralTensorScalarComparison l E F ι X
        ((constructibleIntegralHom l E X).obj PI) PI.obj.1.unop).inv ≫
        S.map ((podIntegralClosed l E X).evaluation PI))) := by
  let := RationalVerdier.units D l hl X
  dsimp only
  let G := RationalVerdier.scalar l X E F ι
  let S := RationalVerdier.integralScalar l X E F ι
  let QE := sfRationalConstructibleLocalization l E X
  let QF := sfRationalConstructibleLocalization l F X
  let PI := integralPairOfRationalHomPair l E X P
  let PF := rationalHomScalarPair l E F ι X P
  let PFI := integralHomScalarPair l E F ι X PI
  let H := (rationalDerivedInternalHom l E X).obj P
  let HI := (constructibleIntegralHom l E X).obj PI
  let HF := (rationalDerivedInternalHom l F X).obj PF
  let HFI := (constructibleIntegralHom l F X).obj PFI
  have hs (M : sfRationalConstructibleCategory l E X) :
      G.obj M = QF.obj (S.obj M.obj) :=
    sfRationalScalarExtension_obj l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι M
  have hH : H = QE.obj HI := by
    simpa only [H, HI, PI, QE, rationalDerivedInternalHom,
      sfRationalConstructibleLocalization, ScalarLocalization.localization] using
      (rationalDerivedInternalHom_existsUnique l E X).exists.choose_spec.1 P
  have hGH : G.obj H = QF.obj (S.obj HI) := by rw [hs, hH]; rfl
  have hW : G.obj P.obj.2 = QF.obj (S.obj PI.obj.2) := hs _
  have htE (M N : sfRationalConstructibleCategory l E X) :
      (rationalDerivedTensor l E X).obj (M, N) =
        QE.obj ((constructibleIntegralTensor l E X).obj (M.obj, N.obj)) := by
    simpa only [rationalDerivedTensor, QE, sfRationalConstructibleLocalization,
      ScalarLocalization.localization] using
      (rationalDerivedTensor_existsUnique l E X).exists.choose_spec.1 (M, N)
  have htarget : G.obj ((rationalDerivedTensor l E X).obj (H, P.obj.1.unop)) =
      QF.obj (S.obj ((constructibleIntegralTensor l E X).obj (HI, PI.obj.1.unop))) := by
    rw [hs, htE, hH]
    rfl
  have heE := rationalEvaluation_normalization l E X P
  have hemap := scalarMap_integral l E F ι X _ _ _ _
    (by
      change (rationalDerivedTensor l E X).obj (H, P.obj.1.unop) = _
      rw [htE, hH]
      rfl) rfl _ _ heE
  have hK : G.obj P.obj.1.unop = QF.obj (S.obj PI.obj.1.unop) := hs _
  have ht (M N : sfRationalConstructibleCategory l F X) :
      (rationalDerivedTensor l F X).obj (M, N) =
        QF.obj ((constructibleIntegralTensor l F X).obj (M.obj, N.obj)) :=
    by simpa only [rationalDerivedTensor, QF, sfRationalConstructibleLocalization,
      ScalarLocalization.localization] using
      (rationalDerivedTensor_existsUnique l F X).exists.choose_spec.1 (M, N)
  have hsrc : (rationalDerivedTensor l F X).obj (G.obj H, G.obj P.obj.1.unop) =
      QF.obj ((constructibleIntegralTensor l F X).obj
        (S.obj HI, S.obj PI.obj.1.unop)) := by rw [ht, hGH, hK]; rfl
  have hi : HEq ((rationalTensorScalarComparison l E F ι X).inv.app
      (H, P.obj.1.unop))
      (QF.map (integralTensorScalarComparison l E F ι X HI PI.obj.1.unop).inv) := by
    have hh : HEq ((rationalTensorScalarComparison l E F ι X).hom.app
        (H, P.obj.1.unop))
        (QF.map (integralTensorScalarComparison l E F ι X H.obj P.obj.1.unop.obj).hom) := by
      simpa only [rationalTensorScalarComparison] using
        (rationalTensorScalarComparison_existsUnique l E F ι X).exists.choose_spec
          H P.obj.1.unop
    have hh' : HEq ((rationalTensorScalarComparison l E F ι X).hom.app
        (H, P.obj.1.unop))
        (QF.map (integralTensorScalarComparison l E F ι X HI PI.obj.1.unop).hom) := by
      have ho := congrArg ScalarLocalization.obj hH
      exact hh.trans (by rw [ho]; rfl)
    exact iso_inv_heq ((rationalTensorScalarComparison l E F ι X).app
      (H, P.obj.1.unop))
      (QF.mapIso (integralTensorScalarComparison l E F ι X HI PI.obj.1.unop))
      htarget hsrc hh'
  exact (heq_comp hsrc htarget hW hi hemap).trans
    (heq_of_eq (QF.map_comp _ _).symm)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Scalar extension preserves the localized Hom-first evaluation square.
Source: finite coefficient comparison and localization in rational Verdier duality
(blueprint: lem-coef-rational-hom-scalar-localized-evaluation).

Proof: identify the endpoints using the scalar, Hom and tensor object formulas.
Tensor bilinearity at coefficient one identifies the tensor of the localized Hom
comparison and identity with the localization of its integral tensor. Normalize
rational evaluation as the localization of integral evaluation. On the other
side, scalar extension on an integral localized map is its integral scalar
extension, and the inverse tensor comparisons agree by uniqueness of inverses.
Compose these heterogeneous equalities and apply localization to the proved
integral evaluation square. No lift of an arbitrary rational arrow is required. -/
theorem rationalHomScalar_localizedEvaluation
    (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (ι : E →ₐ[Padic l] F)
    (P : (constructibleRationalHomPairs l E X).FullSubcategory) :
    letI := RationalVerdier.units D l hl X
    let G := RationalVerdier.scalar l X E F ι
    let H := (rationalDerivedInternalHom l E X).obj P
    let PF := rationalHomScalarPair l E F ι X P
    (rationalDerivedTensor l F X).map
        (Prod.mkHom (rationalHomScalarComparison l E F ι X P).hom
          (𝟙 (G.obj P.obj.1.unop))) ≫
      (podRationalClosed l F X).evaluation PF =
    (rationalTensorScalarComparison l E F ι X).inv.app (H, P.obj.1.unop) ≫
      G.map ((podRationalClosed l E X).evaluation P) := by
  let := RationalVerdier.units D l hl X
  dsimp only
  have h := congrArg (sfRationalConstructibleLocalization l F X).map
    (rationalHomScalar_integralEvaluation D l hl X E F ι
      (integralPairOfRationalHomPair l E X P))
  exact eq_of_heq ((scalarEvaluation_left D l hl X E F ι P).trans
    ((heq_of_eq h).trans (scalarEvaluation_right D l hl X E F ι P).symm))

end WeilConjectures
