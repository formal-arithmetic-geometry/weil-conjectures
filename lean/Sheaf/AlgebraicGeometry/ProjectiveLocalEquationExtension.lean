module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Extension of a local projective equation after a coordinate power

Source: Stacks Project, Tag 03GL, `constructions.tex`, proof of
`lemma-closed-in-projective-space`, converse inclusion of chart ideals.
(blueprint: lem-sfb-projective-local-equation-extension)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MvPolynomial

namespace AlgebraicGeometry

/-- A chart equation of a closed subscheme of projective space extends, after multiplication
by a power of its chart coordinate, to a homogeneous equation vanishing on every chart.
The map to sections of the closed subscheme is `i.app` after `Proj.awayToSection`;
thus vanishing means equality in the section ring, with its nilpotent information.

Source: Stacks Project, Tag 03GL, `lemma-closed-in-projective-space`, converse inclusion.
(blueprint: lem-sfb-projective-local-equation-extension)

Proof plan:
1. Represent `f` as `F / X a ^ d` using the degree-one case of
   `def-nagata-homogeneous-localization-degree-zero`; for zero one may use `d = 0`, `F = 0`.
2. On each chart, closed immersion affineness identifies its inverse image with the spectrum
   of the chart ring modulo the kernel. By `lem-weil-pbc-proj-basic-open-intersection` and
   `lem-weil-pbc-morphism-into-affine-scheme`, its overlap with chart `a` is the principal open
   of the image of `X a / X j`. Clause (0) of `lem-weil-pbc-affine-ideals-closed-subscheme`
   identifies restriction with localization at that element, also for empty charts.
3. On the overlap, `F / X j ^ d = (X a / X j) ^ d * f`; since `f` maps to zero on the
   closed subscheme in chart `a`, this section restricts to zero on the overlap.
4. The kernel criterion of `def-weil-ring-localization-away` gives an exponent `e j`
   annihilating its image in the section ring. On chart `a`, take exponent zero.
5. Take the maximum `N` of these finitely many exponents. Multiplying by the remaining
   powers proves vanishing on every chart. Fraction multiplication gives numerator
   `X a ^ N * F` and denominator `X j ^ (d + N)`. On chart `a` the fraction remains `f`.
   For `n = 0` take `N = 0`; empty charts have the zero section ring. No reducedness,
   Noetherianity, finite presentation or nonemptiness is used. -/
theorem projective_local_equation_extension
    (R : Type u) [CommRing R] (n : ℕ) (Z : Scheme.{u})
    (i : Z ⟶ @Proj _ _ _ _ _ (homogeneousSubmodule (Fin (n + 1)) R)
      (MvPolynomial.gradedAlgebra (σ := Fin (n + 1)) (R := R))) [IsClosedImmersion i]
    (a : Fin (n + 1))
    (f : HomogeneousLocalization.Away (homogeneousSubmodule (Fin (n + 1)) R) (X a))
    (hf : i.app (@Proj.basicOpen _ _ _ _ _ (homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.gradedAlgebra (σ := Fin (n + 1)) (R := R)) (X a))
      (@Proj.awayToSection _ _ _ _ _ (homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.gradedAlgebra (σ := Fin (n + 1)) (R := R)) (X a) f) = 0) :
    ∃ (d N : ℕ) (F : homogeneousSubmodule (Fin (n + 1)) R d),
      f = @HomogeneousLocalization.Away.mk ℕ _ _ _ _ _ _ _
        (homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.gradedAlgebra (σ := Fin (n + 1)) (R := R)) _ _
        (isHomogeneous_X R a) d F (by simp) ∧
      (∀ j : Fin (n + 1),
        i.app (@Proj.basicOpen _ _ _ _ _ (homogeneousSubmodule (Fin (n + 1)) R)
          (MvPolynomial.gradedAlgebra (σ := Fin (n + 1)) (R := R)) (X j))
          (@Proj.awayToSection _ _ _ _ _ (homogeneousSubmodule (Fin (n + 1)) R)
            (MvPolynomial.gradedAlgebra (σ := Fin (n + 1)) (R := R)) (X j)
            (@HomogeneousLocalization.Away.mk ℕ _ _ _ _ _ _ _
              (homogeneousSubmodule (Fin (n + 1)) R)
              (MvPolynomial.gradedAlgebra (σ := Fin (n + 1)) (R := R)) _ _
              (isHomogeneous_X R j) (d + N) (X a ^ N * (F : MvPolynomial (Fin (n + 1)) R))
              (by simpa [Nat.add_comm] using (isHomogeneous_X_pow a N).mul F.property))) = 0) ∧
      f = @HomogeneousLocalization.Away.mk ℕ _ _ _ _ _ _ _
        (homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.gradedAlgebra (σ := Fin (n + 1)) (R := R)) _ _
        (isHomogeneous_X R a) (d + N) (X a ^ N * (F : MvPolynomial (Fin (n + 1)) R))
        (by simpa [Nat.add_comm] using (isHomogeneous_X_pow a N).mul F.property) := by
  sorry

end AlgebraicGeometry
