/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextensionBasis
public import WeilConjectures.NumberTheory.Padics.IntegersAlgebra
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushFiniteFree

/-!
# (Push) for a finite extension of integral coefficients

Let `E ≤ F` be finite subextensions of `ℚ̄_ℓ / ℚ_ℓ`, with rings of integers `𝒪_E ⊆ 𝒪_F`. For an
`𝒪_E`-basis `b₁, …, bₙ` of `𝒪_F`, the map `𝒪̲_Eⁿ ⟶ 𝒪̲_F`, `(xᵢ) ↦ ∑ xᵢ bᵢ`, is an isomorphism of
condensed abelian groups
(`exists_isIso_biproductDesc_finiteCoefficientIntegersPointMap_globalSmul`):
its inverse is given by the coordinates, which are continuous. Hence the comparison **(Push)**
`(Rf_* K)_{𝒪_F} ⟶ Rf_*(K_{𝒪_F})` for the coefficient change `𝒪̲_E ⟶ 𝒪̲_F`
(`AlgebraicGeometry.ProEtale.finiteCoefficientIntegersPointMap`) is an isomorphism for every
morphism of schemes `f` and every `K`
(`AlgebraicGeometry.ProEtale.isIso_derivedPushHom_finiteCoefficientIntegersPointMap`), by
`AlgebraicGeometry.ProEtale.CondensedRing.isIso_derivedPushHom_of_isIso_biproductDesc_globalSmul`.
This is the integral case of blueprint `lemma-change-coefficients-direct-image--3`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonObj Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

attribute [local instance] Abelian.hasFiniteBiproducts

variable (ℓ : ℕ) [Fact ℓ.Prime] {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)

/-- The coordinates of an `𝒪_E`-basis of `𝒪_F` are continuous. -/
lemma continuous_finiteCoefficientIntegralBasis_coord (b : finiteCoefficientIntegralBasis ℓ h)
    (i : Fin (finiteCoefficientDegree ℓ h)) :
    letI := Module.compHom (PadicAlgCl.integers ℓ F.1) (finiteCoefficientIntegersMap ℓ h)
    Continuous (b.coord i) := by
  let := Module.compHom (PadicAlgCl.integers ℓ F.1) (finiteCoefficientIntegersMap ℓ h)
  have : CompactSpace (PadicAlgCl.integers ℓ E.1) := PadicAlgCl.compactSpace_integers ℓ E.1
  have hc : Continuous (b.equivFun.symm :
      (Fin (finiteCoefficientDegree ℓ h) → PadicAlgCl.integers ℓ E.1) →
        PadicAlgCl.integers ℓ F.1) := by
    have heq : (b.equivFun.symm :
        (Fin (finiteCoefficientDegree ℓ h) → PadicAlgCl.integers ℓ E.1) →
          PadicAlgCl.integers ℓ F.1) = fun a ↦ ∑ i, a i • b i := by
      funext a
      exact b.equivFun_symm_apply a
    rw [heq]
    refine continuous_finsetSum _ fun i _ ↦ ?_
    change Continuous (fun a : Fin (finiteCoefficientDegree ℓ h) →
      PadicAlgCl.integers ℓ E.1 ↦ finiteCoefficientIntegersMap ℓ h (a i) * b i)
    have hmap : Continuous (finiteCoefficientIntegersMap ℓ h) :=
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _ |>.subtype_mk _
    exact (hmap.comp (continuous_apply i)).mul_const (b i)
  let e := b.equivFun.symm.toEquiv.toHomeomorphOfContinuousClosed hc hc.isClosedMap
  exact (continuous_apply i).comp e.symm.continuous

/-- **`𝒪̲_F` is a finite free `𝒪̲_E`-module**: for an `𝒪_E`-basis `b` of `𝒪_F`, the map
`𝒪̲_Eⁿ ⟶ 𝒪̲_F`, `(xᵢ) ↦ ∑ xᵢ bᵢ`, is an isomorphism. -/
lemma exists_isIso_biproductDesc_finiteCoefficientIntegersPointMap_mulLeft :
    ∃ (n : ℕ) (b : Fin n → PadicAlgCl.integers ℓ F.1), IsIso (biproduct.desc fun i ↦
      finiteCoefficientIntegersPointMap.{u} ℓ h ≫
        Profinite.continuousMapRingObjMulLeft (PadicAlgCl.integers ℓ F.1) (b i) :
        ⨁ (fun _ : Fin n ↦ Profinite.padicIntegersRingObj.{u} ℓ E.1) ⟶
          Profinite.padicIntegersRingObj ℓ F.1) := by
  obtain ⟨b⟩ := (cartesianCoefficients_finiteFree.{u} ℓ h).1
  let := Module.compHom (PadicAlgCl.integers ℓ F.1) (finiteCoefficientIntegersMap ℓ h)
  let c (i : Fin (finiteCoefficientDegree ℓ h)) :
      Profinite.padicIntegersRingObj.{u} ℓ F.1 ⟶ Profinite.padicIntegersRingObj ℓ E.1 :=
    Profinite.continuousMapRingObjAddMap (b.coord i).toAddMonoidHom
      (continuous_finiteCoefficientIntegralBasis_coord ℓ h b i)
  refine ⟨_, fun i ↦ b i, ⟨biproduct.lift c, ?_, ?_⟩⟩
  · refine biproduct.hom_ext' _ _ fun j ↦ biproduct.hom_ext _ _ fun k ↦ ?_
    simp only [biproduct.ι_desc_assoc, Category.assoc, biproduct.lift_π, Category.comp_id,
      biproduct.ι_π]
    split_ifs with hjk
    · subst hjk
      rw [eqToHom_refl]
      ext S a
      apply ULift.ext
      refine ContinuousMap.ext fun s ↦ ?_
      change b.coord j (b j * finiteCoefficientIntegersMap ℓ h (a.down s)) = a.down s
      rw [mul_comm]
      change b.coord j (a.down s • b j) = a.down s
      simp
    · ext S a
      apply ULift.ext
      refine ContinuousMap.ext fun s ↦ ?_
      change b.coord k (b j * finiteCoefficientIntegersMap ℓ h (a.down s)) = 0
      rw [mul_comm]
      change b.coord k (a.down s • b j) = 0
      simp [hjk]
  · rw [biproduct.lift_desc]
    ext S a
    have h₁ := (sheafToPresheaf (coherentTopology Profinite.{u}) Ab.{u + 1} ⋙
      (evaluation _ _).obj S).map_sum (fun j ↦ c j ≫ finiteCoefficientIntegersPointMap ℓ h ≫
        Profinite.continuousMapRingObjMulLeft (PadicAlgCl.integers ℓ F.1) (b j)) Finset.univ
    refine ULift.ext (ContinuousMap.ext fun s ↦ ?_)
    let ev : (Profinite.padicIntegersRingObj.{u} ℓ F.1).obj.obj S →+
        PadicAlgCl.integers ℓ F.1 :=
      { toFun y := (show ULift.{u + 1} C(S.unop, PadicAlgCl.integers ℓ F.1) from y).down s
        map_zero' := rfl
        map_add' _ _ := rfl }
    have h₂ := congrArg (fun φ ↦ ev (AddCommGrpCat.homAddEquiv φ a)) h₁
    simp only [map_sum, AddMonoidHom.finsetSum_apply] at h₂
    refine h₂.trans ?_
    change ∑ j, b j * finiteCoefficientIntegersMap ℓ h (b.coord j (a.down s)) = a.down s
    simp only [mul_comm (b _), Module.Basis.coord_apply]
    exact b.sum_repr _

/-- **`𝒪̲_F` is a finite free `𝒪̲_E`-module**, in terms of the action of the constant global
sections `bᵢ` of `𝒪̲_F` on the regular module. -/
lemma exists_isIso_biproductDesc_finiteCoefficientIntegersPointMap_globalSmul :
    ∃ (n : ℕ) (b : Fin n → PadicAlgCl.integers ℓ F.1), IsIso (biproduct.desc fun i ↦
      finiteCoefficientIntegersPointMap.{u} ℓ h ≫
        Mod.globalSmul (Profinite.continuousMapConstRingHom (PadicAlgCl.integers ℓ F.1) (b i)).hom
          (Mod.regular (Profinite.padicIntegersRingObj ℓ F.1)) :
        ⨁ (fun _ : Fin n ↦ Profinite.padicIntegersRingObj.{u} ℓ E.1) ⟶
          Profinite.padicIntegersRingObj ℓ F.1) := by
  obtain ⟨n, b, hb⟩ := exists_isIso_biproductDesc_finiteCoefficientIntegersPointMap_mulLeft ℓ h
  refine ⟨n, b, ?_⟩
  simpa only [Profinite.globalSmul_continuousMapConstRingHom] using hb

/-- For finite subextensions `E ≤ F`, the extension of scalars along `𝒪_{E,X} ⟶ 𝒪_{F,X}` is
exact: `𝒪_{F,X}` is finite free over `𝒪_{E,X}`. -/
instance preservesFiniteLimits_extendScalars_finiteCoefficientIntegersPointMap
    (Z : Scheme.{u}) : PreservesFiniteLimits
      (Mod.extendScalars (coefficientMap (finiteCoefficientIntegersPointMap ℓ h) Z)) :=
  ((cartesianCoefficients_finiteFree.{u} ℓ h).2.2 Z).1

/-- Blueprint `lemma-change-coefficients-direct-image--3` for the integral coefficients
`(𝒪_E, 𝒪_F)` of a finite extension `F/E`: the comparison `(Rf_* K)_{𝒪_F} ⟶ Rf_*(K_{𝒪_F})` for
the coefficient change `𝒪̲_E ⟶ 𝒪̲_F` is an isomorphism, for every morphism of schemes `f` and
on all unbounded objects. Indeed `𝒪̲_F` is finite free over `𝒪̲_E`, so both sides are finite
direct sums of copies of `Rf_*^{𝒪_E}`. -/
instance isIso_derivedPushHom_finiteCoefficientIntegersPointMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (CondensedRing.derivedPushHom (finiteCoefficientIntegersPointMap ℓ h) f) :=
  (exists_isIso_biproductDesc_finiteCoefficientIntegersPointMap_globalSmul.{u} ℓ h).elim
    fun _ hn ↦ hn.elim fun b hb ↦
      CondensedRing.isIso_derivedPushHom_of_isIso_biproductDesc_globalSmul
        (finiteCoefficientIntegersPointMap ℓ h)
        (Profinite.continuousMapConstRingHom (PadicAlgCl.integers ℓ F.1)) b hb f

end AlgebraicGeometry.ProEtale
