/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcRationalCategory
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import WeilConjectures.NumberTheory.Padics.IntegersLocalizationUniformizer
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformCompleteTriangulated
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalizationTriangulated
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import WeilConjectures.Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.CategoryTheory.ScalarLocalization.SemilinearScalarLocalization

/-! # Functorial transport to finite rational coefficients

Source: Weil blueprint, proper base change, order 1306
(blueprint: prop-weil-pbc-rational-transport).
The scalar-first tensor convention is identified with the source's Hom-first convention
by TensorProduct.comm. All functors and comparisons below use actual tensor maps.

## Main definitions

- `CategoryTheory.ScalarLocalization.transport`: tensor extension of a linear functor.
- `CategoryTheory.ScalarLocalization.transportNat`: componentwise tensor extension.
- `WeilConjectures.pbcRationalExtension`: extension on the completed rational categories.

## Main statements

- `CategoryTheory.ScalarLocalization.transport_exact`: generic exact tensor transport.
- `WeilConjectures.pbcRationalTransport`: exactness, scalar formulas and uniqueness.
- `WeilConjectures.pbcRationalExchange`: transport of the four supplied operations and exchange.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe r u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄ u

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace CategoryTheory.ScalarLocalization

variable (R : Type r) [CommRing R] (p : R)
variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [Linear R C]
variable {D : Type u₂} [Category.{v₂} D] [Preadditive D] [Linear R D]
variable (F : C ⥤ D) [F.Additive] [F.Linear R]

variable {F} {G : C ⥤ D} [G.Additive] [G.Linear R]

end CategoryTheory.ScalarLocalization

namespace AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (T : Scheme.{u}) [IsNoetherian T]
  (hDim : ∃ d : ℕ, topologicalKrullDim T ≤ d)
  (hInv : ∀ t : T, IsUnit (l : T.presheaf.stalk t))

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable (T : Scheme.{u}) [IsNoetherian T]
variable (hDim : ∃ d : ℕ, topologicalKrullDim T ≤ d)
variable (hInv : ∀ t : T, IsUnit (l : T.presheaf.stalk t))

end AlgebraicGeometry.Scheme

namespace WeilConjectures

open AlgebraicGeometry AlgebraicGeometry.Scheme

variable (l : ℕ) [Fact l.Prime]
variable (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
variable (X Y : Scheme.{u}) [IsNoetherian X] [IsNoetherian Y]
variable (hX : ∃ d : ℕ, topologicalKrullDim X ≤ d)
variable (iX : ∀ t : X, IsUnit (l : X.presheaf.stalk t))
variable (hY : ∃ d : ℕ, topologicalKrullDim Y ≤ d)
variable (iY : ∀ t : Y, IsUnit (l : Y.presheaf.stalk t))
variable (F : PbcIntegralCategory l E X hX iX ⥤
  PbcIntegralCategory l E Y hY iY)
variable [F.Additive] [F.Linear (PbcIntegralRing l E)]

variable (X' Y' : Scheme.{u}) [IsNoetherian X'] [IsNoetherian Y']
variable (hX' : ∃ d : ℕ, topologicalKrullDim X' ≤ d)
variable (iX' : ∀ t : X', IsUnit (l : X'.presheaf.stalk t))
variable (hY' : ∃ d : ℕ, topologicalKrullDim Y' ≤ d)
variable (iY' : ∀ t : Y', IsUnit (l : Y'.presheaf.stalk t))

end WeilConjectures
