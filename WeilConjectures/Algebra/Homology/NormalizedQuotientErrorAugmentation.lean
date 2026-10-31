/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.Ring.Sheaf.PrincipalPowerQuotients
public import WeilConjectures.Algebra.Homology.NormalizedQuotientErrorBasic

/-! # The canonical quotient augmentation for a principal Koszul complex

Source: blueprint sk-lem-sp-tower proof, paragraph 2; Stacks 03CZ and 03EK.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.unusedSectionVars false
universe u v r
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open SheafOfModules.RegularQuotientCone
namespace SheafOfModules.NormalizedQuotientError
variable {S : Type u} [Category.{v} S] {J : GrothendieckTopology S}
  [EssentiallySmall.{r} S]
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]

private theorem projection_power_zero (R : Sheaf J CommRingCat.{r})
    [HasSheafify J CommRingCat.{r}]
    (t : (R.obj ⋙ CategoryTheory.forget CommRingCat.{r}).sections)
    (n : ℕ) (V : Sᵒᵖ) :
    ((principalPowerRingProjection R t n).hom.app V).hom
      ((@id (R.obj.obj V) (t.val V)) ^ n) = 0 := by
  unfold principalPowerRingProjection principalPowerRingQuotient
  change ((toSheafify J (sectionPowerQuotientPresheaf R t n)).app V).hom
    (Ideal.Quotient.mk (sectionPowerIdeal R t n V) _) = 0
  have hz : Ideal.Quotient.mk (sectionPowerIdeal R t n V)
      ((@id (R.obj.obj V) (t.val V)) ^ n) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  erw [hz]
  exact map_zero _

private theorem scalarPower_unit (R : Sheaf J CommRingCat.{r})
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (n : ℕ) (V : Sᵒᵖ) (x : R.obj.obj V) :
    (endoPow (globalSectionMultiplication R t) n).val.app V x =
      x * (@id (R.obj.obj V) (t.val V)) ^ n := by
  induction n with
  | zero => change x = _; simp
  | succ n ih =>
    change (@id (R.obj.obj V)
      ((endoPow (globalSectionMultiplication R t) n).val.app V x)) *
        (@id (R.obj.obj V) (t.val V)) = _
    rw [ih, pow_succ]
    exact mul_assoc _ _ _

private theorem quotient_scalar_zero (R : Sheaf J CommRingCat.{r})
    [HasSheafify J CommRingCat.{r}]
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (T : Sheaf J CommRingCat.{r}) (a : R ⟶ T) (n : ℕ)
    (q : T ≅ principalPowerRingQuotient R (ringSection R t) (n + 1))
    (hq : a ≫ q.hom = principalPowerRingProjection R (ringSection R t) (n + 1)) :
    endoPow (globalSectionMultiplication R t) (n + 1) ≫ ringMap a = 0 := by
  have hz (V : Sᵒᵖ) : (a.hom.app V).hom
      ((@id (R.obj.obj V) (t.val V)) ^ (n + 1)) = 0 := by
    have he := congrArg
      (fun f ↦ (f.hom.app V).hom ((@id (R.obj.obj V) (t.val V)) ^ (n + 1))) hq
    have hi : Function.Injective (q.hom.hom.app V) :=
      (ConcreteCategory.bijective_of_isIso (q.hom.hom.app V)).1
    apply hi
    rw [map_zero]
    exact he.trans (projection_power_zero R (ringSection R t) (n + 1) V)
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (a.hom.app V).hom
    ((endoPow (globalSectionMultiplication R t) (n + 1)).val.app V x) * 1 = 0
  rw [scalarPower_unit, map_mul, hz, mul_zero, mul_one]

set_option maxHeartbeats 1600000 in
-- The actual cone and coefficient restriction retain their full coherence data.
/-- The principal Koszul augmentation with its two specified summand formulas.
Source: blueprint sk-lem-sp-tower proof, paragraph 2; Stacks 03CZ
(blueprint: lem-sp-normalized-quotient-augmentation).

Proof: the section t^(m+1) is zero in the sectionwise quotient by its principal
ideal and remains zero after ring sheafification. The specified ring isomorphism
therefore shows that multiplication by that power followed by ringMap a vanishes.
The single-complex functor preserves this equality. Apply the canonical map from
the cone of the first arrow of this zero-composite pair to its target: it is the
quotient map on the unshifted summand and zero on the shifted summand. -/
theorem exists_quotientAugmentation (R : Sheaf J CommRingCat.{r})
    [HasSheafify J CommRingCat.{r}]
    (t : (unit (derivedChangeRingIndependentCoefficients J R)).sections)
    (T : Sheaf J CommRingCat.{r}) (a : R ⟶ T) (m : ℕ)
    (q : T ≅ principalPowerRingQuotient R (ringSection R t) (m + 1))
    (hq : a ≫ q.hom = principalPowerRingProjection R (ringSection R t) (m + 1)) :
    ∃ g : principalKoszul R t m ⟶
        (CochainComplex.singleFunctor (Modules R) 0).obj
          ((restriction a).obj (unit (derivedChangeRingIndependentCoefficients J T))),
      CochainComplex.mappingCone.inr (principalKoszulScalarComplex R t m) ≫ g =
          (CochainComplex.singleFunctor (Modules R) 0).map (ringMap a) ∧
        (CochainComplex.mappingCone.inl (principalKoszulScalarComplex R t m)).v
          0 (-1) (by decide) ≫ g.f (-1) = 0 := by
  let K : ShortComplex (CochainComplex (Modules R) ℤ) :=
    ShortComplex.mk (principalKoszulScalarComplex R t m)
      ((CochainComplex.singleFunctor (Modules R) 0).map (ringMap a)) (by
        dsimp only [principalKoszulScalarComplex]
        rw [← Functor.map_comp, quotient_scalar_zero R t T a m q hq, Functor.map_zero])
  exact ⟨CochainComplex.mappingCone.descShortComplex K,
    CochainComplex.mappingCone.inr_descShortComplex K,
    CochainComplex.mappingCone.inl_v_descShortComplex_f K 0 (-1) (by decide)⟩

end SheafOfModules.NormalizedQuotientError
