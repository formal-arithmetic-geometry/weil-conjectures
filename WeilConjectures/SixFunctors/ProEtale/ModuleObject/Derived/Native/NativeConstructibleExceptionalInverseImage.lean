/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Rational.RationalRestrictionGlue
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteExceptionalInverseImage
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import Mathlib.CategoryTheory.Adjunction.Restrict
import WeilConjectures.CategoryTheory.Triangulated.BrownRepresentability.RightAdjoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
public import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# The native constructible exceptional inverse image

The finite coefficient functor is the published comparison composite
`Scheme.finiteExceptionalInverseImage`. At non-finite coefficients we restrict the
single Brown adjunction on the native condensed localizing closures. In particular,
the algebraic-closure coefficient is `Profinite.padicAlgClRingObj`, not a category of
common representatives of rationalized coefficient systems.

The restriction and its right adjoint are constructed directly from the native
coefficient predicate; no finite-level system is used in this module.

Source: current blueprint, sec-six-functors-basics/sk-thm-existence/
def-weil-exceptional-inverse-image.md, non-finite Brown restriction paragraph
(blueprint: def-weil-exceptional-inverse-image).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The non-finite condensed coefficients of the exceptional inverse image, allowing
isomorphic presentations. The last clause is the finite-subextension-valued condensed
algebraic closure. Source: the coefficient convention and non-finite paragraph
(blueprint: def-weil-exceptional-inverse-image). -/
def IsNativeExceptionalCoefficient (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] : Prop :=
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℤ_[ℓ])) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj ℚ_[ℓ])) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ℓ E.1)) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
  Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ℓ))

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

omit [IsCommMonObj Λ] in
variable (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  (hcd : BaseFieldFiniteCD ℓ k)
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y) (hΛ : IsNativeExceptionalCoefficient ℓ Λ)

include ℓ hcd hΛ in
section AlgebraicallyClosed

variable [IsAlgClosed k]

end AlgebraicallyClosed

end AlgebraicGeometry.ProEtale.CondensedRing
