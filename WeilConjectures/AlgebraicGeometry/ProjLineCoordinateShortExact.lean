/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Preadditive.Biproducts
import WeilConjectures.AlgebraicGeometry.ProjLineCoordinateKernelFork
import WeilConjectures.AlgebraicGeometry.ProjLineCoordinateQuotientEpi

/-! # The coordinate short exact sequence on the polynomial projective line

## References

* Stacks Project, Tag 01MN.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Tensoring the coordinate sequence with any module remains short exact.
No coherence or flatness assumption on `G` is needed (Stacks, Tag 01MN). -/
theorem exists_proj_coordinate_shortExact
    (k : Type u) [Field k]
    (G : (Proj (MvPolynomial.homogeneousSubmodule (Fin 2) k)).Modules) (z : ℤ) :
    ∃ (f : G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) (z - 1) ⟶
        (G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) z) ⊞
        (G ⊗ Proj.twist (MvPolynomial.homogeneousSubmodule (Fin 2) k) z))
      (h : f ≫ biprod.desc
        (G ◁ Proj.twistMul z (MvPolynomial.X_mem_homogeneousSubmodule_one k (0 : Fin 2)))
        (G ◁ Proj.twistMul z (MvPolynomial.X_mem_homogeneousSubmodule_one k (1 : Fin 2))) = 0),
      (ShortComplex.mk f (biprod.desc
        (G ◁ Proj.twistMul z (MvPolynomial.X_mem_homogeneousSubmodule_one k (0 : Fin 2)))
        (G ◁ Proj.twistMul z (MvPolynomial.X_mem_homogeneousSubmodule_one k (1 : Fin 2))))
        h).ShortExact := by
  obtain ⟨f, h, hf⟩ := exists_proj_coordinate_kernel_fork k G z
  let hf' : IsLimit (KernelFork.ofι f h) := Classical.choice hf
  let g := biprod.desc
    (G ◁ Proj.twistMul z (MvPolynomial.X_mem_homogeneousSubmodule_one k (0 : Fin 2)))
    (G ◁ Proj.twistMul z (MvPolynomial.X_mem_homogeneousSubmodule_one k (1 : Fin 2)))
  have hg : Epi g := by
    dsimp [g]
    exact proj_coordinate_quotient_epi k G z
  let S := ShortComplex.mk f g h
  have he : S.Exact := ShortComplex.exact_of_f_is_kernel S hf'
  let : Mono S.f := mono_of_isLimit_fork hf'
  have hs : S.ShortExact := ShortComplex.ShortExact.mk' he inferInstance hg
  exact ⟨f, h, hs⟩

end AlgebraicGeometry
