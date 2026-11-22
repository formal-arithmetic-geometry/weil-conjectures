/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.SectionFractionPresentation
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import WeilConjectures.AlgebraicGeometry.SectionRingVeroneseFractionKernel

/-! # The Veronese fraction equivalence and its formula on generators

## Implementation details

`sectionRingVeroneseFractionEquiv` is the inverse of the quotient equivalence given by the
first isomorphism theorem for the explicit direct-sum map, whose surjectivity and kernel are
`sectionRingVeroneseFractionMap_surjective` and `sectionRingVeroneseFractionMap_kernel`. No
data are chosen from a bare existence theorem.

## References

* [Stacks, Tags 01PW, 01Q1, 0B5L]
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical Veronese fraction equivalence, inverse to the quotient map sending `t` in
numerator degree `n` to `of_(nd)(T_n⁻¹(t))/s^n`.
-/
noncomputable def sectionRingVeroneseFractionEquiv
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) :
    HomogeneousLocalization.Away (sectionRingGrade L) s.val ≃+
      SectionFractionPresentation (L.tensorPow d) (𝟙_ X.Modules) (s.val d) :=
  (QuotientAddGroup.liftEquiv
    (sectionFractionRelations (L.tensorPow d) (𝟙_ X.Modules) (s.val d)).toAddSubgroup
    (sectionRingVeroneseFractionMap_surjective X L d s)
    (sectionRingVeroneseFractionMap_kernel X L d s)).symm

/-- Formula for the Veronese fraction equivalence on homogeneous generators.
-/
theorem sectionRing_veronese_fraction_formula
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d)
    (e : HomogeneousLocalization.Away (sectionRingGrade L) s.val ≃+
      SectionFractionPresentation (L.tensorPow d) (𝟙_ X.Modules) (s.val d))
    (he : e = sectionRingVeroneseFractionEquiv X L d s) :
    ∀ (n : ℕ) (ξ : sectionRingGrade L (n • d)),
      e (HomogeneousLocalization.Away.mk (sectionRingGrade L) s.property n
        ξ.val ξ.property) =
      sectionFraction (L.tensorPow d) (𝟙_ X.Modules) (s.val d) n
        ((eqToIso (congrArg L.tensorPow (by simp [Nat.mul_comm])) ≪≫
          L.tensorPowMulIso d n ≪≫ (λ_ _).symm).hom.app ⊤ (ξ.val (n • d))) := by
  subst e
  intro n ξ
  apply (sectionRingVeroneseFractionEquiv X L d s).symm.injective
  rw [AddEquiv.symm_apply_apply]
  change _ = sectionRingVeroneseFractionMap X L d s
    (DirectSum.of
      (fun i : ℕ ↦ Γ((𝟙_ X.Modules) ⊗ (L.tensorPow d).tensorPow i, ⊤)) n
      ((sectionRingVeroneseNumeratorIso X L d n).hom.app ⊤ (ξ.val (n • d))))
  simp only [sectionRingVeroneseFractionMap, DirectSum.toAddMonoid_of,
    AddMonoidHom.comp_apply]
  rw [sectionRingVeroneseNumerator_cancel X L d n ξ]
  rfl

end AlgebraicGeometry.Scheme.Modules
