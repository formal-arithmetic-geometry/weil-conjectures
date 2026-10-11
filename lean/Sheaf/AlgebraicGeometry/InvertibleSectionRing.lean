/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The graded section ring of an invertible module

Source: Stacks Project, Tags 01PZ and 01N8
(blueprint: def-sc-invertible-section-ring).

The homogeneous component is literally the global sections of the indicated tensor power.
All operations are specified; only their algebraic laws remain to be proved.

## Main definitions

- `InvertibleSectionRing`: the direct sum of tensor-power sections.
- `sectionRingGCommRing`: tensor multiplication and the degree-zero unit.
- `sectionRingGrade`, `sectionRingGradedRing`: homogeneous components and their grading.
-/

universe u

open CategoryTheory MonoidalCategory DirectSum

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Global sections in degree `n` (Stacks, Tag 01PZ;
(blueprint: def-sc-invertible-section-ring)). -/
noncomputable abbrev SectionRingComponent (L : X.Modules) (n : ℕ) : Type u := Γ(L.tensorPow n, ⊤)

/-- The homogeneous unit is the section `1` of the zeroth tensor power (Stacks, Tag 01PZ;
(blueprint: def-sc-invertible-section-ring)). -/
noncomputable instance sectionRingGOne (L : X.Modules) :
    GradedMonoid.GOne (SectionRingComponent L) where
  one := unitSectionsEquiv ⊤ 1

/-- Homogeneous multiplication tensors sections, then adds tensor exponents (Stacks, Tag 01PZ;
(blueprint: def-sc-invertible-section-ring)). -/
noncomputable instance sectionRingGMul (L : X.Modules) :
    GradedMonoid.GMul (SectionRingComponent L) where
  mul {i j} a b := (L.tensorPowAddIso i j).inv.app ⊤ (tmulSection a b)

/-- Stacks, Tag 01PZ (blueprint: def-sc-invertible-section-ring). The tensor product with zero is
zero; applying the additive tensor-power isomorphism preserves zero. -/
theorem sectionRing_mul_zero (L : X.Modules) [L.IsInvertible]
    {i j : ℕ} (a : SectionRingComponent L i) :
    GradedMonoid.GMul.mul a (0 : SectionRingComponent L j) = 0 := by
  sorry

/-- Stacks, Tag 01PZ (blueprint: def-sc-invertible-section-ring). The tensor product with zero is
zero, and the tensor-power isomorphism is additive. -/
theorem sectionRing_zero_mul (L : X.Modules) [L.IsInvertible]
    {i j : ℕ} (b : SectionRingComponent L j) :
    GradedMonoid.GMul.mul (0 : SectionRingComponent L i) b = 0 := by
  sorry

/-- Stacks, Tag 01PZ (blueprint: def-sc-invertible-section-ring). Distribute the tensor of
sections in its second argument and use additivity of the exponent isomorphism. -/
theorem sectionRing_mul_add (L : X.Modules) [L.IsInvertible]
    {i j : ℕ} (a : SectionRingComponent L i) (b c : SectionRingComponent L j) :
    GradedMonoid.GMul.mul a (b + c) =
      GradedMonoid.GMul.mul a b + GradedMonoid.GMul.mul a c := by
  sorry

/-- Stacks, Tag 01PZ (blueprint: def-sc-invertible-section-ring). Distribute the tensor of
sections in its first argument and use additivity of the exponent isomorphism. -/
theorem sectionRing_add_mul (L : X.Modules) [L.IsInvertible]
    {i j : ℕ} (a b : SectionRingComponent L i) (c : SectionRingComponent L j) :
    GradedMonoid.GMul.mul (a + b) c =
      GradedMonoid.GMul.mul a c + GradedMonoid.GMul.mul b c := by
  sorry

/-- Stacks, Tag 01PZ (blueprint: def-sc-invertible-section-ring). The degree-zero section is the
monoidal unit; the left unitor and the exponent isomorphism cancel. -/
theorem sectionRing_one_mul (L : X.Modules) [L.IsInvertible]
    (a : GradedMonoid (SectionRingComponent L)) :
    1 * a = a := by
  sorry

/-- Stacks, Tag 01PZ (blueprint: def-sc-invertible-section-ring). The right unitor identifies
tensoring with the section one with the identity; coherence cancels the exponent isomorphism. -/
theorem sectionRing_mul_one (L : X.Modules) [L.IsInvertible]
    (a : GradedMonoid (SectionRingComponent L)) :
    a * 1 = a := by
  sorry

/-- Stacks, Tag 01PZ (blueprint: def-sc-invertible-section-ring). The associator sends (a tensor
b) tensor c to a tensor (b tensor c). The exponent isomorphisms agree by monoidal coherence,
including the equality of the two degree sums. -/
theorem sectionRing_mul_assoc (L : X.Modules) [L.IsInvertible]
    (a b c : GradedMonoid (SectionRingComponent L)) :
    a * b * c = a * (b * c) := by
  sorry

/-- Stacks, Tag 01PZ (blueprint: def-sc-invertible-section-ring). Locally trivialize the
invertible module. Both products then multiply the same two functions in the commutative structure
sheaf, times the same tensor power of the chosen generator. These equalities glue; commutation of
the degree sum supplies the dependent equality. -/
theorem sectionRing_mul_comm (L : X.Modules) [L.IsInvertible]
    (a b : GradedMonoid (SectionRingComponent L)) :
    a * b = b * a := by
  sorry

/-- The graded commutative ring laws on tensor-power sections (Stacks, Tag 01PZ;
(blueprint: def-sc-invertible-section-ring)). All operations are explicit; the law fields
refer to the preceding named theorems and the additive-group cast identities. -/
noncomputable instance sectionRingGCommRing (L : X.Modules) [L.IsInvertible] :
    DirectSum.GCommRing (SectionRingComponent L) where
  mul_zero := sectionRing_mul_zero L
  zero_mul := sectionRing_zero_mul L
  mul_add := sectionRing_mul_add L
  add_mul := sectionRing_add_mul L
  one_mul := sectionRing_one_mul L
  mul_one := sectionRing_mul_one L
  mul_assoc := sectionRing_mul_assoc L
  mul_comm := sectionRing_mul_comm L
  natCast n := n • (GradedMonoid.GOne.one : SectionRingComponent L 0)
  natCast_zero := zero_nsmul _
  natCast_succ n := succ_nsmul _ n
  intCast z := z • (GradedMonoid.GOne.one : SectionRingComponent L 0)
  intCast_ofNat n := natCast_zsmul _ n
  intCast_negSucc_ofNat n := negSucc_zsmul _ n

/-- The section ring `⨁ n, Γ(X, L^{⊗ n})` (Stacks, Tag 01PZ;
(blueprint: def-sc-invertible-section-ring)). -/
noncomputable abbrev InvertibleSectionRing (L : X.Modules) :=
  ⨁ n : ℕ, SectionRingComponent L n

/-- The homogeneous component inside the section ring (Stacks, Tag 01PZ;
(blueprint: def-sc-invertible-section-ring)). -/
noncomputable def sectionRingGrade (L : X.Modules) (n : ℕ) :
    AddSubgroup (InvertibleSectionRing L) :=
  (DirectSum.of (SectionRingComponent L) n).range

/-- The homogeneous components form a multiplicative grading (Stacks, Tag 01PZ;
(blueprint: def-sc-invertible-section-ring)). The unit is in degree zero by construction.
The product of two single-component sums is the single-component sum of their tensor product,
so its degree is the sum of the two degrees. -/
theorem sectionRing_gradedMonoid (L : X.Modules) [L.IsInvertible] :
    SetLike.GradedMonoid (sectionRingGrade L) := by
  sorry

/-- The section ring is the internal direct sum of its homogeneous components (Stacks, Tag 01PZ;
(blueprint: def-sc-invertible-section-ring)). Every finitely supported section family is the
sum of its single-component families. Evaluation in each degree shows this expression is
unique. Thus the canonical recomposition map is bijective. -/
theorem sectionRing_isInternal (L : X.Modules) :
    DirectSum.IsInternal (sectionRingGrade L) := by
  sorry

/-- The grading on the section ring, using the inverse of the bijective recomposition map
(Stacks, Tag 01PZ; (blueprint: def-sc-invertible-section-ring)). -/
noncomputable instance sectionRingGradedRing (L : X.Modules) [L.IsInvertible] :
    GradedRing (sectionRingGrade L) :=
  { sectionRing_gradedMonoid L,
    (sectionRing_isInternal L).chooseDecomposition with }

end AlgebraicGeometry.Scheme.Modules
