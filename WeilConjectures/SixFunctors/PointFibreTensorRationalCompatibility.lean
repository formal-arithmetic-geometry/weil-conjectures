/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSixTensorComparison
public import WeilConjectures.SecSmoothPurity.TransportScalar

/-! # Rational point-fibre tensor and unit compatibility

Source: `literature/blueprint/latest/blueprint/sec-six-functors-basics/
  sk-prop-scalar-six/det-prop-scalar-six-tensor-hom.proof.md`, clause (1),
  specialized to the geometric point (blueprint: def-sf-point-fibre-tensor-rational-compatibility).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- A condensed scalar-six ring is rational when it is isomorphic to a finite
subextension coefficient ring or to the finite-subextension-valued algebraic closure ring.
Source: the rational coefficient alternatives in the scalar-six point setting
(blueprint: def-sf-point-fibre-tensor-rational-compatibility). -/
def IsRationalCoefficient (ell : ℕ) [Fact ell.Prime] (Λ : ScalarSixRing.{u}) : Prop :=
  (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Λ ≅ (Coefficient.rational E).bundled.{u} ell)) ∨
    Nonempty (Λ ≅ Coefficient.closure.bundled.{u} ell)

/-- Equality of supplied rational point-fibre tensorators and unit comparisons with the
canonical scalar-six structure, for every rational coefficient map, including identities.
Source: the K-flat tensor comparison and coefficient-unit normalization in clause (1) of
`det-prop-scalar-six-tensor-hom.proof.md`, specialized to `Spec D.k`
(blueprint: def-sf-point-fibre-tensor-rational-compatibility). -/
def pointFibreTensorRationalCompatibility
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (_hell : ell ≠ D.p)
    (b : ∀ (Λ Λ' : ScalarSixRing.{u})
      (_hΛ : IsRationalCoefficient.{u} ell Λ)
      (_hΛ' : IsRationalCoefficient.{u} ell Λ')
      (c : Λ ⟶ Λ')
      (K M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X
        (Spec (.of D.k)))),
      (scalarSixChange c (Spec (.of D.k))).obj (K ⊗ M) ≅
        (scalarSixChange c (Spec (.of D.k))).obj K ⊗
          (scalarSixChange c (Spec (.of D.k))).obj M)
    (v : ∀ (Λ Λ' : ScalarSixRing.{u})
      (_hΛ : IsRationalCoefficient.{u} ell Λ)
      (_hΛ' : IsRationalCoefficient.{u} ell Λ')
      (c : Λ ⟶ Λ'),
      (scalarSixChange c (Spec (.of D.k))).obj (𝟙_ _) ≅ 𝟙_ _) : Prop :=
  (∀ (Λ Λ' : ScalarSixRing.{u})
      (hΛ : IsRationalCoefficient.{u} ell Λ)
      (hΛ' : IsRationalCoefficient.{u} ell Λ')
      (c : Λ ⟶ Λ')
      (K M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X
        (Spec (.of D.k)))),
    b Λ Λ' hΛ hΛ' c K M = scalarSixTensorIso c (Spec (.of D.k)) K M) ∧
    (∀ (Λ Λ' : ScalarSixRing.{u})
      (hΛ : IsRationalCoefficient.{u} ell Λ)
      (hΛ' : IsRationalCoefficient.{u} ell Λ')
      (c : Λ ⟶ Λ'),
    v Λ Λ' hΛ hΛ' c = (Functor.Monoidal.εIso (scalarSixChange c (Spec (.of D.k)))).symm)

end AlgebraicGeometry.ProEtale.CondensedRing
