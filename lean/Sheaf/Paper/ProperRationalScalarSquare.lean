/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q59
-/
module

public import Sheaf.Paper.ProperCoefficientDescentData

/-! # Descent of the proper comparison through coefficient stages -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.ProperCoefficientDescent
open AlgebraicallyClosedCoefficients (Index Coefficient)
open GeneralAlgebraicallyClosedCoefficients
open TensorProduct

variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]


private theorem scalar_obj (W : Scheme.{u}) (E L : Index l Ω) (h : E ≤ L)
    (K : Stage l Ω W E) :
    (stageTransition l Ω W E L h).obj K =
      ⟨(integralTransition l Ω W E L h).obj K.obj⟩ := by
  unfold stageTransition stageSystem
  rw [(stageSystem_existsUnique l Ω W).exists.choose_spec.1 E L h]
  exact (sfRationalScalarExtension_existsUnique l (Coefficient.{u} l Ω E) W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h)).exists.choose_spec.2.1 K

private theorem scalar_map (W : Scheme.{u}) (E L : Index l Ω) (h : E ≤ L)
    {K M : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) W} (a : K ⟶ M) :
    HEq ((stageTransition l Ω W E L h).map
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) W).map a))
      ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) W).map
        ((integralTransition l Ω W E L h).map a)) := by
  unfold stageTransition stageSystem
  rw [(stageSystem_existsUnique l Ω W).exists.choose_spec.1 E L h]
  have hh := (sfRationalScalarExtension_existsUnique l (Coefficient.{u} l Ω E) W 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) (Coefficient.{u} l Ω L)
    (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω E L h)).exists.choose_spec.2.2
      K M a 1
  simpa only [map_one, transition, sfRationalScalarExtension, integralTransition,
    sfRationalConstructibleLocalization, ScalarLocalization.localization] using hh

private theorem map_heq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B A' B' : C} {a : A ⟶ B} {b : A' ⟶ B'}
    (hA : A = A') (hB : B = B') (h : HEq a b) : HEq (F.map a) (F.map b) := by
  cases hA
  cases hB
  cases h
  rfl

private theorem inverse_heq {C : Type*} [Category C] {A B A' B' : C}
    (e : A ≅ B) (e' : A' ≅ B') (hA : A = A') (hB : B = B')
    (h : HEq e.hom e'.hom) : HEq e.inv e'.inv := by
  cases hA
  cases hB
  have he : e = e' := Iso.ext (eq_of_heq h)
  cases he
  rfl

private theorem apply_heq {A : Sort*} {B : A → Sort*}
    (g : ∀ a, B a) {a b : A} (h : a = b) : HEq (g a) (g b) := by
  cases h
  rfl

section Descent
variable (B : FiniteFieldDatum.{u}) (hl : l ≠ B.p)
  {X Y : Scheme.{u}} [X.Over (Spec (.of B.k))] [Y.Over (Spec (.of B.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of B.k))] [QuasiCompact (X ↘ Spec (.of B.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of B.k))] [QuasiCompact (Y ↘ Spec (.of B.k))]
  [IsSeparated (X ↘ Spec (.of B.k))] [IsSeparated (Y ↘ Spec (.of B.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of B.k))] [IsProper f]


omit [IsSeparated (X ↘ Spec (.of B.k))] [IsSeparated (Y ↘ Spec (.of B.k))] in
/-- Localizing the integral scalar square gives compatibility on rational stages.
Source: current blueprint, prop-weil-proper-compact-coincidence.proof.md,
first paragraph; coefficient-descent argument, Step 5.
(blueprint: lem-weil-proper-rational-scalar-square).

Proof: evaluate the integral square on the underlying integral object and apply
target rationalization. The rational transitions are the semilinear extensions of
the integral transitions, hence their action on one tensor a is one tensor its
integral image. The compact rationalBeta field identifies the left scalar comparison;
HasComparisonLaws identifies the ordinary comparison, including its inverse. The
given component formulas identify the two rationalized theta maps. Functoriality
of localization preserves the composition equality. Transport along the prescribed
stage-system equalities gives precisely the displayed square. -/
theorem rationalScalarSquare
    (D : SfStrictDirectImageScalar.IntegralComparisons l Ω f)
    (R : SfStrictDirectImageScalar.Comparisons l Ω f D)
    (hR : SfStrictDirectImageScalar.HasComparisonLaws l Ω f D R)
    (S : SfCompactSupportCoefficientAction l B.k
      (PurCompactSupport.coefficientPrimeUnit l B hl) Ω (Compactification.ofIsProper f))
    (θ : ∀ E : Index l Ω, compactIntegral l Ω B hl f E ≅ (D.integral E).image)
    (hI : ∀ (E L : Index l Ω) (h : E ≤ L)
      (K : sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) X),
      (integralTransition l Ω Y E L h).map ((θ E).hom.app K) ≫
          (D.integralComparison E L h).inv.app K =
        (S.integralBeta h).hom.app K ≫
          (θ L).hom.app ((integralTransition l Ω X E L h).obj K))
    (r : ∀ E : Index l Ω, S.system.Φ E ≅ R.rational E)
    (hr : ∀ (E : Index l Ω) (K : Stage l Ω X E),
      HEq ((r E).hom.app K)
        ((sfRationalConstructibleLocalization l (Coefficient.{u} l Ω E) Y).map
          ((θ E).hom.app K.obj)))
    (β : ∀ {E L : Index l Ω} (h : E ≤ L),
      R.rational E ⋙ stageTransition l Ω Y E L h ≅
        stageTransition l Ω X E L h ⋙ R.rational L)
    (hβ : ∀ (E L : Index l Ω) (h : E ≤ L) (K : Stage l Ω X E),
      HEq ((β h).hom.app K) ((R.theta E L h).inv.app K)) :
    ∀ (E L : Index l Ω) (h : E ≤ L) (K : Stage l Ω X E),
      HEq ((stageTransition l Ω Y E L h).map ((r E).hom.app K) ≫
        (β h).hom.app K)
        ((S.system.β h).hom.app K ≫
          (r L).hom.app ((stageTransition l Ω X E L h).obj K)) := by
  intro E L h K
  let QL := sfRationalConstructibleLocalization l (Coefficient.{u} l Ω L) Y
  let TX := integralTransition l Ω X E L h
  let TY := integralTransition l Ω Y E L h
  let K' := (stageTransition l Ω X E L h).obj K
  have hK : K' = ⟨TX.obj K.obj⟩ := scalar_obj l Ω X E L h K
  have hF (e : Index l Ω) (A : Stage l Ω X e) :
      (S.system.Φ e).obj A =
        ⟨(compactIntegral l Ω B hl f e).obj A.obj⟩ := by
    rw [S.finite_eq]
    rfl
  have hm : HEq ((stageTransition l Ω Y E L h).map ((r E).hom.app K))
      (QL.map (TY.map ((θ E).hom.app K.obj))) :=
    (map_heq _ (hF E K) (hR.1 E K) (hr E K)).trans
      (scalar_map l Ω Y E L h ((θ E).hom.app K.obj))
  have hsrc : (stageTransition l Ω Y E L h).obj ((S.system.Φ E).obj K) =
      QL.obj (TY.obj ((compactIntegral l Ω B hl f E).obj K.obj)) := by
    rw [scalar_obj, hF]
    rfl
  have hmid : (stageTransition l Ω Y E L h).obj ((R.rational E).obj K) =
      QL.obj (TY.obj ((D.integral E).image.obj K.obj)) := by
    rw [scalar_obj, hR.1]
    rfl
  have htgt : (R.rational L).obj K' = QL.obj ((D.integral L).image.obj (TX.obj K.obj)) := by
    rw [hR.1, hK]
    rfl
  have hmid' : (S.system.Φ L).obj K' =
      QL.obj ((compactIntegral l Ω B hl f L).obj (TX.obj K.obj)) := by
    rw [hF, hK]
    rfl
  have ho : HEq ((β h).hom.app K)
      (QL.map ((D.integralComparison E L h).inv.app K.obj)) := by
    apply (hβ E L h K).trans
    apply inverse_heq ((R.theta E L h).app K)
      (QL.mapIso ((D.integralComparison E L h).app K.obj))
    · change (R.rational L).obj
        ((transition l Ω X E L h).obj K) = _
      have hx := (stageSystem_existsUnique l Ω X).exists.choose_spec.1 E L h
      rw [← hx]
      exact htgt
    · change (transition l Ω Y E L h).obj ((R.rational E).obj K) = _
      have hy := (stageSystem_existsUnique l Ω Y).exists.choose_spec.1 E L h
      rw [← hy]
      exact hmid
    · exact hR.2.2.2.2.1 E L h K
  have ht : HEq ((r L).hom.app K')
      (QL.map ((θ L).hom.app (TX.obj K.obj))) := by
    apply (hr L K').trans
    exact apply_heq (fun A ↦ QL.map ((θ L).hom.app A))
      (congrArg (fun A : Stage l Ω X L ↦ A.obj) hK)
  have hb : HEq ((S.system.β h).hom.app K)
      (QL.map ((S.integralBeta h).hom.app K.obj)) := S.rationalBeta h K
  exact (heq_comp hsrc hmid htgt hm ho).trans
    ((heq_of_eq (by rw [← QL.map_comp, hI, QL.map_comp])).trans
      (heq_comp hsrc hmid' htgt hb ht).symm)

end Descent
end WeilConjectures.ProperCoefficientDescent
