/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.KummerModuleCoefficients
import Sheaf.AlgebraicGeometry.KummerFiniteFreeComparison

/-!
# Integral basis comparison of the Kummer root sheaf

Source: Stacks Tag 03EK and the quotient-ring tensor identity.
(blueprint: lem-pur-kummer-integral-root-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

/-- Reduction of an integral basis gives the normalized left-term comparison.
Source: blueprint lem-pur-kummer-coefficient-base-change, step 7; Stacks Tag 03EK.
Proof: reduce every integral coordinate b_j^* modulo m. Each coordinate vanishes
on mL, so descends to L/mL and transports along e to a coordinate c_j on A.
Every residue-ring scalar is an integer cast, so these additive coordinates are
R-linear. On v_i=e([b_i]) their values are the Kronecker coefficients. Lifting a
to L and reducing the integral basis expansion proves sum_j c_j(a) v_j=a.
Apply the normalized dual-basis sheaf comparison to these vectors and coordinates.
Its inclusion formula is precisely the required normalization. For rank zero both
objects vanish; m=0 is the integral basis comparison and m=1 is the zero-module case.
(blueprint: lem-pur-kummer-integral-root-comparison). -/
theorem kummer_integral_root_comparison (C : Scheme.{u}) (m : ℕ)
    (A : ModuleCat.{u + 1} (ULift.{u + 1} (ZMod m)))
    (L : ModuleCat.{u + 1} ℤ) (r : ℕ) (b : Module.Basis (Fin r) ℤ L)
    (e : (L ⧸ LinearMap.range ((m : ℤ) • (LinearMap.id : L →ₗ[ℤ] L))) ≃ₗ[ℤ] A)
    [HasBiproduct (fun _ : Fin r ↦ C.rootsOfUnitySheaf m)] :
    ∃ theta : (⨁ fun _ : Fin r ↦ C.rootsOfUnitySheaf m) ≅
        (kummerAbelianTwist C m).obj A,
      ∀ j : Fin r, biproduct.ι (fun _ : Fin r ↦ C.rootsOfUnitySheaf m) j ≫ theta.hom =
        kummerCoefficientInsertion C m A (e (Submodule.Quotient.mk (b j))) := by
  classical
  let R := ULift.{u + 1} (ZMod m)
  let K := LinearMap.range ((m : ℤ) • (LinearMap.id : L →ₗ[ℤ] L))
  let d (j : Fin r) : L →ₗ[ℤ] R :=
    (Int.castAddHom R).toIntLinearMap.comp (b.coord j)
  have hd (j : Fin r) : K ≤ LinearMap.ker (d j) := by
    rintro y ⟨l, rfl⟩
    change d j ((m : ℤ) • l) = 0
    simp [d]
  let c0 (j : Fin r) : A →ₗ[ℤ] R :=
    ((K.liftQ (d j) (hd j)).toAddMonoidHom.comp e.symm.toAddMonoidHom).toIntLinearMap
  let c (j : Fin r) : A →ₗ[R] R :=
    { __ := (c0 j).toAddMonoidHom
      map_smul' := by
        intro t a
        obtain ⟨n, hn⟩ := ZMod.intCast_surjective t.down
        have ht : (n : R) = t := ULift.ext _ _ hn
        rw [← ht]
        exact map_intCast_smul (c0 j) R R n a }
  let v (j : Fin r) := e (Submodule.Quotient.mk (b j))
  have hc_mk (j : Fin r) (l : L) :
      c j (e (Submodule.Quotient.mk l)) = (b.repr l j : R) := by
    change (K.liftQ (d j) (hd j)) (e.symm (e (Submodule.Quotient.mk l))) = _
    rw [e.symm_apply_apply]
    rfl
  have hcv (i j : Fin r) : c j (v i) = if i = j then 1 else 0 := by
    dsimp only [v]
    rw [hc_mk]
    simp only [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs
    · exact Int.cast_one
    · exact Int.cast_zero
  have hc (a : A) : ∑ j, c j a • v j = a := by
    obtain ⟨l, hl⟩ := K.mkQ_surjective (e.symm a)
    have ha : a = e (Submodule.Quotient.mk l) := by
      exact ((congrArg e hl).trans (e.apply_symm_apply a)).symm
    subst a
    simp_rw [hc_mk]
    change (∑ j, (b.repr l j : R) • e (Submodule.Quotient.mk (b j))) = _
    simp_rw [Int.cast_smul_eq_zsmul R]
    let vadd : L →+ A := e.toAddEquiv.toAddMonoidHom.comp K.mkQ.toAddMonoidHom
    change (∑ j, (b.repr l j) • vadd (b j)) = vadd l
    calc
      _ = vadd (∑ j, (b.repr l j) • b j) := by simp only [map_sum, map_zsmul]
      _ = vadd l := congrArg vadd (by
        calc
          _ = ∑ j, L.isModule.smul (b.repr l j) (b j) := by
            apply Finset.sum_congr rfl
            intro j _
            exact (int_smul_eq_zsmul L.isModule _ _).symm
          _ = l := b.sum_repr l)
  exact kummer_dual_basis_sheaf_comparison C m A v c hcv hc

end AlgebraicGeometry.Scheme
