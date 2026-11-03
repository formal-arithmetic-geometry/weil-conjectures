/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurTwistCanonicalMaps

/-! # Canonical finite root quotients
Source: coefficient twists, canonical comparisons.
(blueprint: lem-pur-finite-root-reductions)
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj
namespace AlgebraicGeometry.ProEtale

/-- Canonical finite root-power maps and Tate residue projections are scalar quotient
comparisons.
Source: def-coefficient-twists-detailed, finite-exponent independence and the projection
comparison T_S tensor Z/ell^r; companion local-freeness proof, steps 1 and 2.
(blueprint: lem-pur-finite-root-reductions).
Proof: choose the compatible primitive-root cover. A root at level a+k is sent to
its ell^k-th power, the chosen root at level a. On constant cyclic groups this is
residue reduction Z/ell^(a+k) to Z/ell^a. The free module on either group is the
cokernel of that exponent on the coefficient module. If ell^a kills the coefficients,
both cokernels are the regular module and the comparison preserves its generator,
hence is the identity. This proves the first assertion for every positive increment.
For the second assertion, the compatible root bases identify the whole Tate tower
with the regular residue tower. Its limit is the continuous Z_ell coefficient module,
with the recorded reductions as projections. Apply the scalar adjunction to the r-th
projection. The resulting map is the regular scalar-extension isomorphism, since it
sends 1 tensor b to b. Pullback commutes with scalar extension; its adjunction-unit
identity identifies this map with the specified tateTensorReduction, rather than
merely some isomorphism of its endpoints. Detect isomorphisms on the cover. Empty
schemes have the same argument on the empty covering; r>0 ensures the quotient
coefficient object is the one used in its definition. -/
theorem pur_finite_root_reductions
    (S : Scheme.{u}) (ell : ℕ) [Fact ell.Prime]
    (E : Type u) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E]
    [∀ x : S, Invertible (ell : S.residueField x)] :
    (∀ (n r k : ℕ),
      (ell ^ (r + 1) : Padic.coefficientExtensionRing ell E (n + 1)) = 0 →
        IsIso (coefficientFiniteRootComparison ell E S n r (k + 1))) ∧
    (∀ (r : ℕ) (hr : 0 < r), IsIso (tateTensorReduction S ell r hr)) := by sorry

end AlgebraicGeometry.ProEtale
