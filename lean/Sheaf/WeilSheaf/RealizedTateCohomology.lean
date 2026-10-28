/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.WeilSheaf.CoefficientRealizationData
public import Sheaf.WeilSheaf.CoefficientEndpointObjects
public import WeilConjectures.WeilSheaf.TateTwist

/-! # The Tate cohomology of a unit-normalized equivariant realization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
attribute [local instance 1100] CategoryTheory.instOverClass
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.NativeCoefficientCohomology

variable (P : PurityFiniteSetting.{u})
  (X₀ : Over (Spec (.of P.field.k₀)))
  [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
  [Fact (ringChar P.field.k₀ ≠ P.coefficients.l)]

/-- Any additive, shift-compatible equivariant ordinary realization normalized
on the scalar unit has the specified Tate endpoint.

Source: cor-pur-adic-and-rational-smooth-dualizing-complexes.proof.md,
constant-unit identification; the canonical root-line convention of
lem-pur-constant-purity-frobenius-square. No smooth purity is used here.
(blueprint: lem-sf-realized-tate-cohomology)

Proof: trivialize the geometric Tate line by a compatible system of roots of
unity in the algebraically closed geometric field. On its d-th tensor power
the geometric Frobenius map is multiplication by q^(-d), where q is the finite
base field's cardinality. Apply the pullback-unit and tensor-unit comparisons
in canonicalSourceTheta. They identify the unshifted source with the scalar
unit carrying this scalar Frobenius action; this calculation is independent of
the choice of roots since a different basis conjugates a scalar action.

An additive functor preserves multiplication by q^d and the inverse of that
invertible endomorphism. It therefore preserves multiplication by q^(-d);
no extra choice of a scalar-linear structure is required. Naturality of its
Frobenius comparison and Data.unit identify the realized pair with the native
constant pair with the same scalar action, namely the native d-th Tate sheaf
tensor the native constant. Data.shift and Data.frobeniusShift transport the
even shift by 2d, including its action. Degree -2d cohomology of this shifted
degree-zero sheaf is the original sheaf by the single-functor homology
isomorphism. Compose these identifications to obtain the stated pair
isomorphism. For d=0 all comparisons are the specified unit maps; on the empty
scheme the same maps are the unique isomorphisms between zero objects. -/
theorem realized_tate_cohomology (R : CoefficientRealization.Data P X₀) (d : ℕ) :
    Nonempty
      ((CoefficientRealization.pairCohomology P X₀ R (-2 * (d : ℤ))).obj
          (twistedConstant P X₀ d) ≅
        ((WeilSheaf.tateTwistSheaf P.field.k₀ P.coefficients.l X₀.left d).tensorObj
          (WeilSheaf.adicConstant P.field.k₀ P.coefficients.l X₀.left)
          (WeilSheaf.isLisse_tateTwistSheaf P.field.k₀ P.coefficients.l X₀.left d)).obj) := by sorry

end WeilConjectures.NativeCoefficientCohomology
