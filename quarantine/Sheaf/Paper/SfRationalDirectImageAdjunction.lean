/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.Paper.WeilIndSheafCategory
public import WeilConjectures.CategoryTheory.StageSystem.Functor
import Sheaf.Paper.SfIntegralPullbackLinearAdjunction
import Sheaf.Paper.SfRationalDirectImageCoefficientCompatibility
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.LinearAlgebra.TensorProduct.Map

/-! # Finite rational derived adjunctions

Source: Bhatt--Scholze 6.7.2, 6.8.14(2), Remark 6.8.15.
(blueprint: lem-sf-rational-direct-image-adjunctions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits TensorProduct
namespace CategoryTheory
variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]
  {A : Type u₃} [Category.{v₃} A]
  {B : Type u₄} [Category.{v₄} B]
  {P : Type u₅} [Category.{v₅} P]
  {Q : Type u₆} [Category.{v₆} Q]

variable [Preadditive C] [Preadditive D]
  {F : C ⥤ D} {G : D ⥤ C} [G.Additive]

private theorem additiveLeftOfLinearRight (a : F ⊣ G) : F.Additive where
  map_add {X Y} f g := by
    apply (a.homEquiv _ _).injective
    have hh (v : X ⟶ Y) : a.homEquiv _ _ (F.map v) = v ≫ a.unit.app Y := by
      rw [a.homEquiv_unit]
      exact (a.unit.naturality v).symm
    rw [hh, a.homEquiv_unit, G.map_add, Preadditive.comp_add, ← a.homEquiv_unit,
      ← a.homEquiv_unit, hh, hh, Preadditive.add_comp]

omit [G.Additive] in
private theorem linearLeftOfLinearRight (R : Type*) [CommRing R] [Linear R C] [Linear R D]
    [G.Linear R] (a : F ⊣ G) : F.Linear R where
  map_smul {X Y} f r := by
    apply (a.homEquiv _ _).injective
    have hh (v : X ⟶ Y) : a.homEquiv _ _ (F.map v) = v ≫ a.unit.app Y := by
      rw [a.homEquiv_unit]
      exact (a.unit.naturality v).symm
    rw [hh, a.homEquiv_unit, G.map_smul, Linear.comp_smul, ← a.homEquiv_unit,
      hh, Linear.smul_comp]

end CategoryTheory


universe r u v w x
namespace CategoryTheory.ScalarLocalization
variable (R : Type r) [CommRing R] (p : R)
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear R C]
  {D : Type w} [Category.{x} D] [Preadditive D] [Linear R D]

private def liftLinear (F : C ⥤ D) [F.Additive] [F.Linear R] :
    ScalarLocalization R C p ⥤ ScalarLocalization R D p where
  obj X := ⟨F.obj X.obj⟩
  map {X Y} := (F.mapLinearMap R).baseChange (Localization.Away p)
  map_id X := by
    change (F.mapLinearMap R).baseChange (Localization.Away p) (1 ⊗ₜ[R] 𝟙 X.obj) = _
    rw [LinearMap.baseChange_tmul]
    change (1 : Localization.Away p) ⊗ₜ[R] F.map (𝟙 X.obj) =
      (1 : Localization.Away p) ⊗ₜ[R] 𝟙 (F.obj X.obj)
    rw [F.map_id]
  map_comp {X Y Z} f g := by
    change (F.mapLinearMap R).baseChange (Localization.Away p)
      (composition R C p X.obj Y.obj Z.obj g f) =
      composition R D p _ _ _
        ((F.mapLinearMap R).baseChange (Localization.Away p) g)
        ((F.mapLinearMap R).baseChange (Localization.Away p) f)
    induction g using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply]
    | tmul b g =>
      induction f using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul a f =>
        simp only [composition_tmul, LinearMap.baseChange_tmul,
          Functor.coe_mapLinearMap]
        change (b * a) ⊗ₜ[R] F.map (f ≫ g) =
          (b * a) ⊗ₜ[R] (F.map f ≫ F.map g)
        rw [F.map_comp]
      | add f g hf hg => simp only [_root_.map_add, hf, hg]
    | add f g hf hg => simp only [_root_.map_add, LinearMap.add_apply, hf, hg]

@[simp] private theorem liftLinear_tmul (F : C ⥤ D) [F.Additive] [F.Linear R]
    {X Y : ScalarLocalization R C p} (a : Localization.Away p) (f : X.obj ⟶ Y.obj) :
    (liftLinear R p F).map (a ⊗ₜ[R] f) = a ⊗ₜ[R] F.map f := by
  change (F.mapLinearMap R).baseChange (Localization.Away p) (a ⊗ₜ[R] f) = _
  simpa only [Functor.coe_mapLinearMap] using
    (LinearMap.baseChange_tmul (F.mapLinearMap R) a f)

private instance liftLinear_additive (F : C ⥤ D) [F.Additive] [F.Linear R] :
    (liftLinear R p F).Additive where
  map_add {X Y f g} := by
    change (F.mapLinearMap R).baseChange (Localization.Away p) (f + g) = _
    exact _root_.map_add _ f g

private def liftAdjunction (F : C ⥤ D) [F.Additive] [F.Linear R]
    (G : D ⥤ C) [G.Additive] [G.Linear R] (adj : F ⊣ G) :
    liftLinear R p F ⊣ liftLinear R p G where
  unit :=
    { app X := 1 ⊗ₜ[R] adj.unit.app X.obj
      naturality {X Y} f := by
        dsimp only [liftLinear, Functor.id_obj, Functor.comp_obj]
        change composition R C p _ _ _
          (1 ⊗ₜ[R] adj.unit.app Y.obj) f =
          composition R C p _ _ _
            ((G.mapLinearMap R).baseChange (Localization.Away p)
              ((F.mapLinearMap R).baseChange (Localization.Away p) f))
            (1 ⊗ₜ[R] adj.unit.app X.obj)
        induction f using TensorProduct.induction_on with
        | zero => simp only [map_zero, LinearMap.zero_apply]
        | tmul a f =>
          simp only [LinearMap.baseChange_tmul, Functor.coe_mapLinearMap,
            composition_tmul, one_mul, mul_one]
          exact congrArg (fun k ↦ a ⊗ₜ[R] k) (adj.unit.naturality f)
        | add f g hf hg => simp only [_root_.map_add, LinearMap.add_apply, hf, hg] }
  counit :=
    { app X := 1 ⊗ₜ[R] adj.counit.app X.obj
      naturality {X Y} f := by
        dsimp only [liftLinear, Functor.id_obj, Functor.comp_obj]
        change composition R D p _ _ _
          (1 ⊗ₜ[R] adj.counit.app Y.obj)
            ((F.mapLinearMap R).baseChange (Localization.Away p)
              ((G.mapLinearMap R).baseChange (Localization.Away p) f)) =
          composition R D p _ _ _ f (1 ⊗ₜ[R] adj.counit.app X.obj)
        induction f using TensorProduct.induction_on with
        | zero => simp only [map_zero, LinearMap.zero_apply]
        | tmul a f =>
          simp only [LinearMap.baseChange_tmul, Functor.coe_mapLinearMap,
            composition_tmul, one_mul, mul_one]
          exact congrArg (fun k ↦ a ⊗ₜ[R] k) (adj.counit.naturality f)
        | add f g hf hg => simp only [_root_.map_add, LinearMap.add_apply, hf, hg] }
  left_triangle_components X := by
    change composition R D p _ _ _ (1 ⊗ₜ[R] adj.counit.app (F.obj X.obj))
      ((liftLinear R p F).map (1 ⊗ₜ[R] adj.unit.app X.obj)) = _
    rw [liftLinear_tmul, composition_tmul, one_mul]
    exact congrArg (fun k ↦ (1 : Localization.Away p) ⊗ₜ[R] k)
      (adj.left_triangle_components X.obj)
  right_triangle_components X := by
    change composition R C p _ _ _
      ((liftLinear R p G).map (1 ⊗ₜ[R] adj.counit.app X.obj))
      (1 ⊗ₜ[R] adj.unit.app (G.obj X.obj)) = _
    rw [liftLinear_tmul, composition_tmul, one_mul]
    exact congrArg (fun k ↦ (1 : Localization.Away p) ⊗ₜ[R] k)
      (adj.right_triangle_components X.obj)
end CategoryTheory.ScalarLocalization

open AlgebraicGeometry
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of K₀))]
  [∀ x : X, Invertible (l : X.residueField x)]
  [∀ y : Y, Invertible (l : Y.residueField y)]

include K₀ hl in
private theorem rationalSystemPullback_isLeftAdjoint :
    (rationalDerivedPullback l E f).IsLeftAdjoint := by
  let I := constructibleIntegralPullback l E f
  obtain ⟨R, ⟨a⟩, hAdd, hLin⟩ := sfIntegralPullbackLinearAdjunction l E K₀ hl f
  have : R.Additive := hAdd
  have : R.Linear (Padic.coefficientExtensionIntegers l E) := hLin
  have : I.Additive := CategoryTheory.additiveLeftOfLinearRight a
  have : I.Linear (Padic.coefficientExtensionIntegers l E) :=
    CategoryTheory.linearLeftOfLinearRight _ a
  let p := Padic.coefficientExtensionUniformizer l E
  let O := Padic.coefficientExtensionIntegers l E
  let Lq := ScalarLocalization.liftLinear O p I
  have heq : Lq = rationalDerivedPullback l E f := by
    apply (rationalDerivedPullback_existsUnique l E f).unique _
      (rationalDerivedPullback_existsUnique l E f).exists.choose_spec
    refine ⟨inferInstance, (fun _ ↦ rfl), ?_⟩
    intro K N b c
    exact heq_of_eq (ScalarLocalization.liftLinear_tmul O p I c b)
  let aq := ScalarLocalization.liftAdjunction O p I R a
  have : Lq.IsLeftAdjoint := ⟨_, ⟨aq⟩⟩
  rwa [← heq]

end WeilConjectures

namespace WeilConjectures
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients

/-- Finite rational adjunctions with their scalar-change mate equations.
Source: Bhatt--Scholze 6.7.2, 6.8.14(2), Remark 6.8.15
(blueprint: lem-sf-rational-direct-image-adjunctions).
Proof: use the normalized integral adjunction on the full constructible categories.
Its right functor is coefficient-linear, so the adjunction makes pullback additive
and coefficient-linear. Tensor the unit and counit with one in the raw Hom
localization; tensor induction proves naturality and both triangles. The pure-tensor
characterization identifies the localized left functor with the recorded rational
pullback. Apply this pointwise construction to the uniquely normalized left family,
then use the separate coefficient-change theorem for its right-adjoint mates.
The common-stage quotient and Weil lifting are not used. -/
theorem sfRationalDirectImageAdjunctions
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] (f : X₀ ⟶ Y₀) :
    letI := sfWeilPrimeInvertible D l hl X₀
    letI := sfWeilPrimeInvertible D l hl Y₀
    ∃ (L : (stageSystem l Ω (D.geometricFiber Y₀).left).Morphism
        (stageSystem l Ω (D.geometricFiber X₀).left))
      (R : ∀ E : Index l Ω,
        sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
            (D.geometricFiber X₀).left ⥤
          sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
            (D.geometricFiber Y₀).left),
      L.Φ = (fun E ↦ rationalDerivedPullback l (Coefficient.{u} l Ω E) (zlFiberMap D f)) ∧
      (∀ (E F : Index l Ω) (h : E ≤ F)
        (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
          (D.geometricFiber Y₀).left),
        HEq ((L.β h).app K)
          (commonStagePullbackComparison l Ω (zlFiberMap D f) ⟨E, K⟩ F h)) ∧
      ∃ (a : ∀ E, L.Φ E ⊣ R E)
        (β : ∀ {E F : Index l Ω} (h : E ≤ F),
          R E ⋙ (stageSystem l Ω (D.geometricFiber Y₀).left).T h ≅
            (stageSystem l Ω (D.geometricFiber X₀).left).T h ⋙ R F),
        ∀ {E F : Index l Ω} (h : E ≤ F)
          (K : sfRationalConstructibleCategory l (Coefficient.{u} l Ω E)
            (D.geometricFiber X₀).left),
          (L.Φ F).map ((β h).hom.app K) ≫
              (a F).counit.app
                (((stageSystem l Ω (D.geometricFiber X₀).left).T h).obj K) =
            (L.β h).inv.app ((R E).obj K) ≫
              ((stageSystem l Ω (D.geometricFiber X₀).left).T h).map
                ((a E).counit.app K) := by
  let := sfWeilPrimeInvertible D l hl X₀
  let := sfWeilPrimeInvertible D l hl Y₀
  obtain ⟨L, ⟨hΦ, hβ, hm⟩, _⟩ :=
    sfRationalDirectImageCoefficientCompatibility D l hl Ω f
  have hunit : IsUnit (l : D.k) := by
    let : Fintype D.k₀ := Fintype.ofFinite D.k₀
    have : Fact D.p.Prime := ⟨D.prime⟩
    have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
    have : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
    exact (CharP.cast_ne_zero_of_ne_of_prime D.k (Fact.out : l.Prime) hl.symm).isUnit
  have : (zlFiberMap D f).IsOver (Spec (.of D.k)) :=
    ⟨((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map f).w⟩
  have : LocallyOfFiniteType ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) := by
    change LocallyOfFiniteType (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    infer_instance
  have : QuasiCompact ((D.geometricFiber X₀).left ↘ Spec (.of D.k)) := by
    change QuasiCompact (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    infer_instance
  have : LocallyOfFiniteType ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) := by
    change LocallyOfFiniteType (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    infer_instance
  have : QuasiCompact ((D.geometricFiber Y₀).left ↘ Spec (.of D.k)) := by
    change QuasiCompact (pullback.snd Y₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    infer_instance
  have hpoint (E : Index l Ω) : (L.Φ E).IsLeftAdjoint := by
    rw [hΦ]
    exact rationalSystemPullback_isLeftAdjoint l (Coefficient.{u} l Ω E) D.k
      hunit (X := (D.geometricFiber X₀).left) (Y := (D.geometricFiber Y₀).left)
      (zlFiberMap D f)
  let R E := @Functor.rightAdjoint _ _ _ _ (L.Φ E) (hpoint E)
  let a E : L.Φ E ⊣ R E := @Adjunction.ofIsLeftAdjoint _ _ _ _ (L.Φ E) (hpoint E)
  let β {E F : Index l Ω} (h : E ≤ F) :
      R E ⋙ (stageSystem l Ω (D.geometricFiber Y₀).left).T h ≅
        (stageSystem l Ω (D.geometricFiber X₀).left).T h ⋙ R F := by
    let := hm R a h
    exact asIso ((mateEquiv (a E) (a F) (TwoSquare.mk _ _ _ _ (L.β h).inv)).natTrans)
  refine ⟨L, R, hΦ, hβ, a, β, ?_⟩
  intro E F h K
  exact mateEquiv_counit (a E) (a F) (TwoSquare.mk _ _ _ _ (L.β h).inv) K

end WeilConjectures
