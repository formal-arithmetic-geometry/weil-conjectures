/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SmoothPurityCoefficientTowersAbelian
public import WeilConjectures.AlgebraicGeometry.SmoothPurityNormalizedTowers
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothAdjunctionData
public import WeilConjectures.AlgebraicGeometry.ProEtaleTateTwistsOfUniverses
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.AlgebraicGeometry.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom

/-! # General-field geometric adjunction and native operation comparisons on strict towers

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/sk-thm-purity-transport/
 sk-thm-purity-transport.proof.md`, Step 2, geometric tower model and actual integral
operations; the all-perfect-field version of the tower geometric construction is WANTED
(blueprint: lem-dla1-native-condensed-integral-transport).

The statement records the strict tower adjunction, its finite evaluations, and the native
coefficient comparisons.  It imposes no absolute cohomological-dimension hypothesis.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.NativeCondensedIntegralTransport

/-- The strict normalized tower category attached to a finite coefficient extension. -/
abbrev Tower (ell : ℕ) [Fact ell.Prime] (E : Type u) [Field E]
    [Algebra (Padic ell) E] [FiniteDimensional (Padic ell) E] (T : Scheme.{u}) :=
  spNormalizedConstructibleTorTowerCategory ell E T
    (Classical.choice (sp_coefficient_towers_abelian ell E T))

variable (ell : ℕ) [Fact ell.Prime]

/-- Geometric data used by the transport statement. -/
structure Geometry where
  k : Type u
  [field : Field k]
  [perfect : PerfectField k]
  invertible : IsUnit (ell : k)
  E : Type u
  [e_field : Field E]
  [e_algebra : Algebra (Padic ell) E]
  [e_finite : FiniteDimensional (Padic ell) E]
  X : Over (Spec (.of k))
  Y : Over (Spec (.of k))
  [separatedX : IsSeparated X.hom]
  [separatedY : IsSeparated Y.hom]
  [finiteX : LocallyOfFiniteType X.hom]
  [finiteY : LocallyOfFiniteType Y.hom]
  [qcX : QuasiCompact X.hom]
  [qcY : QuasiCompact Y.hom]
  f : X.left ⟶ Y.left
  [isOver : f.IsOver (Spec (.of k))]
  [separated : IsSeparated f]
  [finite : LocallyOfFiniteType f]
  [qc : QuasiCompact f]
  r : ℕ
  [smooth : SmoothOfRelativeDimension r f]
  compactification : Compactification f

attribute [instance] Geometry.field Geometry.perfect Geometry.e_field Geometry.e_algebra
  Geometry.e_finite Geometry.separatedX Geometry.separatedY Geometry.finiteX Geometry.finiteY
  Geometry.qcX Geometry.qcY Geometry.isOver Geometry.separated Geometry.finite Geometry.qc
  Geometry.smooth

/-- Data expressing actual strict-system operations and their canonical comparison maps. -/
structure Transport (ell : ℕ) [Fact ell.Prime] (g : Geometry ell) where
  F : Tower ell g.E g.X.left ⥤ Tower ell g.E g.Y.left
  J : Tower ell g.E g.Y.left ⥤ Tower ell g.E g.X.left
  adjunction : Nonempty (F ⊣ J)
  finite_evaluation : ∀ _n : ℕ, Nonempty (F ⟶ F)
  quotient_cocycle : ∀ _n m : ℕ, _n ≤ m → Nonempty (F ⟶ F)
  nativeF : Type u
  nativeJ : Type u
  nativeF_map : nativeF → nativeF
  nativeJ_map : nativeJ → nativeJ
  reductionF : ∀ _n : ℕ, Nonempty (nativeF → nativeF)
  reductionJ : ∀ _n : ℕ, Nonempty (nativeJ → nativeJ)
  scalar_extension : ∀ (K L : Type u), Nonempty (K → L)
  scheme_isomorphism_naturality : ∀ (K : Type u), K = K
  compactification_refinement : ∀ (K : Type u), K = K

/-- STATEMENT-DISPUTED: the generated interface requires a function `K → L` for
 every pair of types `K` and `L`.  This is false: take `K := PUnit` and
 `L := Empty`; a function would produce an element of `Empty`.  The theorem
 remains unchanged so that the false interface is not silently weakened.

General-field tower adjunction and native integral transport.
Source: geometric tower model and actual integral operations (blueprint:
lem-dla1-native-condensed-integral-transport). -/
theorem native_condensed_integral_transport (ell : ℕ) [Fact ell.Prime]
    (g : Geometry ell) : Nonempty (Transport ell g) := by
  sorry

end AlgebraicGeometry.ProEtale.NativeCondensedIntegralTransport
