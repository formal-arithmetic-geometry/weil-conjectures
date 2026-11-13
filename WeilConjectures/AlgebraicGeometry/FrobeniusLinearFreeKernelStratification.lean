/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import Mathlib.Algebra.Category.Grp.Ulift
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.CharP.Basic
import WeilConjectures.AlgebraicGeometry.EtaleSpecQuotientSolutions
import WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite
import WeilConjectures.AlgebraicGeometry.EtaleUpperStarRepresentableFiniteLocallyConstant
import WeilConjectures.AlgebraicGeometry.FrobeniusLinearFreeKernelCoordinates
import WeilConjectures.RingTheory.FrobeniusPolynomialEtale

/-!
# Frobenius-linear fixed points in an affine free frame

## References

* Stacks Project, Tags 0GKU and 03S0.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Fixed points in an affine finite free frame admit a finite constructible stratification.
(Stacks, Tag 0GKU) -/
theorem frobenius_linear_free_kernel_stratification
    (p : ℕ) [Fact p.Prime] (S : Scheme.{u}) [IsAffine S] [CharP Γ(S, ⊤) p]
    (E : S.Modules) [E.IsQuasicoherent]
    (F : (Modules.etaleTensorSectionsSheaf E) ⟶ Modules.etaleTensorSectionsSheaf E)
    (hF : ∀ (U : S.Etale) (a : Γ(U.left, ⊤))
      (e : Γ((Modules.tensorPullback U.hom).obj E, ⊤)),
      F.hom.app (op U)
          ((((Modules.tensorPullback U.hom).obj E).smul a).asHom.hom e) =
        (((Modules.tensorPullback U.hom).obj E).smul (a ^ p)).asHom.hom
          (F.hom.app (op U) e))
    (n : ℕ) (α : E ≅
      SheafOfModules.free (R := S.ringCatSheaf) (ULift.{u} (Fin n))) :
    ∃ T : Stratification S, ∀ k : Fin T.n,
      IsFiniteLocallyConstantSheafOfTypes
        ((sheafCompose (T.domain k).smallEtaleTopology
          (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
          ((Etale.upperStar AddCommGrpCat.{u + 1} (T.immersion k)).obj
            ((sheafCompose S.smallEtaleTopology
              AddCommGrpCat.uliftFunctor.{u + 1, u}).obj (kernel (F - 𝟙 _))))) := by
  classical
  obtain ⟨a, c, hc⟩ := exists_frobenius_linear_free_kernel_coordinates p S E F hF n α
  let f : Fin n → MvPolynomial (Fin n) Γ(S, ⊤) :=
    fun i ↦ MvPolynomial.X i - ∑ j, MvPolynomial.C (a i j) * MvPolynomial.X j ^ p
  have hA : Algebra.Etale Γ(S, ⊤)
      (MvPolynomial (Fin n) Γ(S, ⊤) ⧸ Ideal.span (Set.range f)) := by
    have hf : f = fun i ↦ MvPolynomial.C 0 + MvPolynomial.X i -
        ∑ j, MvPolynomial.C (a i j) * MvPolynomial.X j ^ p := by
      funext i
      rw [map_zero, zero_add]
    rw [hf]
    exact Algebra.frobenius_polynomial_etale Γ(S, ⊤) p n a 0
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤)
      (MvPolynomial (Fin n) Γ(S, ⊤) ⧸ Ideal.span (Set.range f))))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr hA
  have : Etale (specQuotientStructureMap f) := by
    unfold specQuotientStructureMap
    infer_instance
  let P : S.Etale := Etale.mk (specQuotientStructureMap f)
  let K := kernel (F - 𝟙 _)
  let eqv (U : S.Etale) : K.obj.obj (op U) ≃ (U ⟶ P) :=
    (c U).trans ((Equiv.subtypeEquivRight fun x ↦ by simp [f, sub_eq_zero]).trans
      (etaleHomSpecQuotientEquiv f U).symm)
  have heqv (U W : S.Etale) (g : W ⟶ U) (s : K.obj.obj (op U)) :
      eqv W (K.obj.map g.op s) = g ≫ eqv U s := by
    apply (etaleHomSpecQuotientEquiv f W).injective
    ext i
    rw [etaleHomSpecQuotientEquiv_comp]
    simp only [eqv, Equiv.trans_apply]
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    exact hc U W g s i
  let e : (sheafCompose S.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj
      ((sheafCompose S.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj K) ≅
      S.smallEtaleTopology.uliftYoneda.{u + 1}.obj P :=
    (fullyFaithfulSheafToPresheaf _ _).preimageIso (NatIso.ofComponents
      (fun U ↦ (Equiv.ulift.trans ((eqv U.unop).trans Equiv.ulift.symm)).toIso) (by
        intro U W g
        ext s
        exact congrArg ULift.up (heqv U.unop W.unop g.unop s.down)))
  obtain ⟨T, -, hT⟩ := exists_etale_stratified_finite (specQuotientStructureMap f)
  refine ⟨T, fun k ↦ ?_⟩
  have : IsFinite (pullback.snd P.hom (T.immersion k)) := (hT k).1
  exact isFiniteLocallyConstant_forget_upperStar_of_iso_uliftYoneda (T.immersion k) _ P e

end AlgebraicGeometry.Scheme
