/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Flat.Basic
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Universal
public import WeilConjectures.Blowup.Gluing

/-!
# The blow-up as the relative `Proj` of the Rees algebra

For a quasi-coherent ideal `I : X.IdealSheafData`, the Rees algebras `⨁ₙ I(U)ⁿ` of the ideals
`I(U)` over the affine opens `U` form a quasi-coherent graded algebra
`AlgebraicGeometry.Scheme.IdealSheafData.reesData I`: the restriction maps are base changes since
`Γ(X, V) → Γ(X, U)` is flat and `I(U) = I(V) Γ(X, U)`. Its relative `Proj` is the blow-up
`I.blowup` (`AlgebraicGeometry.Scheme.IdealSheafData.relProjReesIso`).

## Main results

- `AlgebraicGeometry.reesGrading.isGradedBaseChangeAlong_hom` — for a flat ring map `φ` and
  `J = I.map φ`, the Rees algebra of `J` is the coefficientwise base change of that of `I`.
- `AlgebraicGeometry.Scheme.IdealSheafData.reesData` — the Rees algebra of a quasi-coherent ideal.
- `AlgebraicGeometry.Scheme.IdealSheafData.relProjReesIso` — `Proj_X(⨁ Iⁿ) ≅ Bl_I X` over `X`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry

variable {A B : Type u} [CommRing A] [CommRing B] {I : Ideal A} {J : Ideal B}

/-- The coefficient of `Xⁿ`, as a linear map on the degree-`n` piece of the Rees algebra. -/
noncomputable def reesCoeff (I : Ideal A) (n : ℕ) : reesGrading I n →ₗ[A] A where
  toFun F := ((F : reesAlgebra I) : Polynomial A).coeff n
  map_add' F G := by simp
  map_smul' c F := by simp

lemma reesCoeff_injective (I : Ideal A) (n : ℕ) : Function.Injective (reesCoeff I n) := by
  intro F G hFG
  obtain ⟨a, ha, hF⟩ := (mem_reesGrading_iff_exists I).mp F.2
  obtain ⟨b, hb, hG⟩ := (mem_reesGrading_iff_exists I).mp G.2
  have hab : a = b := by
    simpa [reesCoeff, hF, hG] using hFG
  subst hab
  exact Subtype.ext (hF.trans hG.symm)

/-- **Rees algebras commute with flat base change**: for a flat ring homomorphism `φ : A →+* B`
and `J = I.map φ`, the induced map of Rees algebras is a coefficientwise base change, i.e.
`B ⊗_A Iⁿ ≅ Jⁿ`. -/
theorem reesGrading.isGradedBaseChangeAlong_hom (φ : A →+* B) (hφ : φ.Flat)
    (h : I.map φ = J) : (reesGrading.hom φ h).IsGradedBaseChangeAlong φ := by
  let := φ.toAlgebra
  let : Algebra A (reesAlgebra J) := ((algebraMap B (reesAlgebra J)).comp φ).toAlgebra
  have : IsScalarTower A B (reesAlgebra J) := .of_algebraMap_eq' rfl
  have : Module.Flat A B := hφ
  have hma : ∀ r : A, reesGrading.hom φ h (algebraMap A (reesAlgebra I) r) =
      algebraMap A (reesAlgebra J) r := fun r ↦ Subtype.ext <| by
    change ((algebraMap A (reesAlgebra I) r : reesAlgebra I) : Polynomial A).map φ =
      ((algebraMap B (reesAlgebra J) (φ r) : reesAlgebra J) : Polynomial B)
    simp
  refine ⟨hma, fun n ↦ ?_⟩
  set f := (reesGrading.hom φ h).degreeLinearMap hma n
  have hcoeff : ∀ x : B ⊗[A] reesGrading I n,
      reesCoeff J n (f.liftBaseChange B x) =
        Algebra.TensorProduct.rid A B B ((reesCoeff I n).lTensor B x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c F =>
      simp only [LinearMap.liftBaseChange_tmul, map_smul, LinearMap.lTensor_tmul,
        Algebra.TensorProduct.rid_tmul]
      change (((c • f F : reesGrading J n) : reesAlgebra J) : Polynomial B).coeff n =
        reesCoeff I n F • c
      simp [f, reesCoeff, Algebra.smul_def, mul_comm]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hinj : Function.Injective (f.liftBaseChange B) := by
    refine Function.Injective.of_comp (f := reesCoeff J n) ?_
    have h1 : Function.Injective ((reesCoeff I n).lTensor B) :=
      Module.Flat.lTensor_preserves_injective_linearMap _ (reesCoeff_injective I n)
    have h2 := (Algebra.TensorProduct.rid A B B).injective.comp h1
    convert h2 using 1
    funext x
    exact hcoeff x
  have hsurj : Function.Surjective (f.liftBaseChange B) := by
    intro z
    obtain ⟨b, hb, hz⟩ := (mem_reesGrading_iff_exists J).mp z.2
    have hb' : b ∈ (I ^ n).map φ := by rwa [Ideal.map_pow, h]
    suffices ∀ (b : B) (hb' : b ∈ (I ^ n).map φ), ∃ x,
        ((f.liftBaseChange B x : reesGrading J n) : reesAlgebra J) =
          reesMonomial J b (by rwa [Ideal.map_pow, h] at hb') by
      obtain ⟨x, hx⟩ := this b hb'
      exact ⟨x, Subtype.ext (hx.trans hz.symm)⟩
    intro b hb'
    induction hb' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      refine ⟨1 ⊗ₜ ⟨reesMonomial I a ha, reesMonomial_mem I a ha⟩, ?_⟩
      simp only [LinearMap.liftBaseChange_tmul, one_smul]
      exact reesGrading.hom_reesMonomial φ h a ha
    | zero => exact ⟨0, Subtype.ext (by simp)⟩
    | add u v hu hv ihu ihv =>
      obtain ⟨x, hx⟩ := ihu
      obtain ⟨y, hy⟩ := ihv
      exact ⟨x + y, by rw [map_add, Submodule.coe_add, hx, hy]; exact Subtype.ext (by simp)⟩
    | smul c u hu ih =>
      obtain ⟨x, hx⟩ := ih
      refine ⟨c • x, ?_⟩
      rw [map_smul, Submodule.coe_smul, hx]
      exact Subtype.ext (by simp [Polynomial.smul_monomial])
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩) fun x ↦ by simp

/-- The degree-zero identification of the Rees algebra is its algebra structure. -/
lemma algebraMap_reesGrading_zero (I : Ideal A) :
    algebraMap A (reesGrading I 0) = (reesGradingZero I).toRingHom :=
  RingHom.ext fun a ↦ Subtype.ext <| Subtype.ext <| by
    change ((algebraMap A (reesAlgebra I) a : reesAlgebra I) : Polynomial A) = _
    simp

lemma Proj.toSpecOfAlgebra_reesGrading (I : Ideal A) :
    Proj.toSpecOfAlgebra (reesGrading I) = AffineBlowup.toSpec I := by
  rw [Proj.toSpecOfAlgebra, AffineBlowup.toSpec, algebraMap_reesGrading_zero]

namespace Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)

lemma flat_presheaf_map {U V : X.affineOpens} (h : U ≤ V) :
    (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom.Flat := by
  have := HasRingHomProperty.appLE (P := @Flat) (𝟙 X) inferInstance V U
    (show U.1 ≤ (𝟙 X) ⁻¹ᵁ V.1 from h)
  rwa [Scheme.Hom.appLE, Scheme.Hom.id_app, Category.id_comp] at this

/-- The **Rees algebra** `⨁ₙ Iⁿ` of a quasi-coherent ideal, as a quasi-coherent graded algebra:
over an affine open `U` it is the Rees algebra of `I(U)`. -/
noncomputable def reesData : X.GradedAlgebraData where
  obj U := reesAlgebra (I.ideal U)
  commRing U := inferInstance
  algebra U := inferInstance
  grading U := reesGrading (I.ideal U)
  gradedAlgebra U := reesGrading.instGradedRing _
  res h := reesGrading.hom (X.presheaf.map (homOfLE (X := X.Opens) h).op).hom (I.map_ideal h)
  res_id U x := by
    have e : (X.presheaf.map (homOfLE (X := X.Opens) (le_refl U)).op).hom =
        RingHom.id Γ(X, U.1) := by
      rw [show homOfLE (X := X.Opens) (le_refl U) = 𝟙 U.1 from Subsingleton.elim _ _,
        op_id, X.presheaf.map_id, CommRingCat.hom_id]
    exact DFunLike.congr_fun ((reesGrading.hom_congr e _).trans reesGrading.hom_id) x
  res_res {U V W} h₁ h₂ x := by
    have e : ((X.presheaf.map (homOfLE (X := X.Opens) h₁).op).hom).comp
        (X.presheaf.map (homOfLE (X := X.Opens) h₂).op).hom =
        (X.presheaf.map (homOfLE (X := X.Opens) (h₁.trans h₂)).op).hom := by
      rw [← CommRingCat.hom_comp, ← Functor.map_comp, ← op_comp]
      rfl
    have := DFunLike.congr_fun (reesGrading.hom_comp _ _ (I.map_ideal h₂) (I.map_ideal h₁)) x
    rw [GradedRingHom.comp_apply] at this
    exact this.trans (DFunLike.congr_fun (reesGrading.hom_congr e _) x)
  isGradedBaseChangeAlong h :=
    reesGrading.isGradedBaseChangeAlong_hom _ (flat_presheaf_map h) _

lemma toOpen_reesData (U : X.affineOpens) :
    I.reesData.toOpen U = I.blowupNatTrans.app U := by
  rw [GradedAlgebraData.toOpen_eq, blowupNatTrans_app]
  exact congrArg (· ≫ _) (Proj.toSpecOfAlgebra_reesGrading (I.ideal U))

lemma isPullback_blowupι_reesData (U : X.affineOpens) :
    IsPullback (I.reesData.toOpen U) (I.blowupι U) U.1.ι I.blowupMap := by
  rw [toOpen_reesData]
  exact I.isPullback_blowupι U

lemma relProjFunctor_map_blowupι {U V : X.affineOpens} (h : U ≤ V) :
    I.reesData.relProjFunctor.map (homOfLE h) ≫ I.blowupι V = I.blowupι U :=
  colimit.w I.blowupFunctor (homOfLE h)

/-- **The blow-up is the relative `Proj` of the Rees algebra**: `Proj_X(⨁ₙ Iⁿ) ≅ Bl_I X`,
compatibly with the charts over the affine opens of `X`. -/
noncomputable def relProjReesIso : I.reesData.relProj ≅ I.blowup :=
  I.reesData.relProjIsoOfIsPullback I.blowupMap I.blowupι I.isPullback_blowupι_reesData
    I.relProjFunctor_map_blowupι

@[reassoc (attr := simp)]
lemma relProjι_relProjReesIso_hom (U : X.affineOpens) :
    I.reesData.relProjι U ≫ I.relProjReesIso.hom = I.blowupι U :=
  I.reesData.relProjι_relProjIsoOfIsPullback_hom _ _ _ _ U

/-- The isomorphism `relProjReesIso` lies over `X`. -/
@[reassoc (attr := simp)]
lemma relProjReesIso_hom_blowupMap :
    I.relProjReesIso.hom ≫ I.blowupMap = I.reesData.relProjHom :=
  I.reesData.relProjIsoOfIsPullback_hom_comp _ _ _ _

end Scheme.IdealSheafData

end AlgebraicGeometry
