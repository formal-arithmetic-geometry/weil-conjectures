/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSlicePresentation
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAmbientRingedExchange
public import WeilConjectures.AlgebraicGeometry.Projection.ProjectionFormulaCompactified
public import WeilConjectures.AlgebraicGeometry.Stratum.StratumScalarExtension
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.AlgebraicGeometry.Picard.DerivedChangeOfRingsIndependentCoefficients
public import WeilConjectures.Algebra.Homology.Derived.DerivedChangeOfRingsGeneral

/-! # Constant-ring pro-etale scalar and open operations

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
lem-fix-compact-support-coefficient-change.proof.md, first paragraph (open-immersion factor
of the compactification and the derived tensor comparison); construction references
Stacks Tags 06YY, 07A6, 07A4, 08FJ and 03DJ
(blueprint: def-sp-open-scalar-operations).

All declarations live in the namespace `AlgebraicGeometry.ProEtale.OpenScalarOperations`,
so they do not clash with the withdrawn `OpenScalarExchange` attachment. The constant
coefficient ring map is the existing `Scheme.proEtaleConstantRingMap`
(def-sp-proetale-constant-coefficient-ring-map).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

namespace OpenScalarOperations

attribute [instance] Scheme.proEtaleRingRestrictScalars_preservesFiniteLimits
  Scheme.proEtaleRingRestrictScalars_preservesFiniteColimits

/-- Derived extension of scalars `S_T = L(- ⊗_{A_T} B_T) : D(A_T) ⥤ D(B_T)` along the
constant ring map induced by `φ`: the universal (pointwise) left derived functor of the
termwise change of rings supplied by lem-pur-derived-change-of-rings. It is characterized
by its universal counit, so the choice is unique up to the unique counit-compatible
isomorphism. No flatness or boundedness is imposed.
Source: Stacks Tags 06YY and 06XN (blueprint: def-sp-open-scalar-operations). -/
noncomputable def scalarExtension {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    Scheme.proEtaleDerivedCategory T A ⥤ Scheme.proEtaleDerivedCategory T B := by
  let h := SheafOfModules.derivedChangeOfRingsGeneral
    (C := T.ProEt) (J := Scheme.ProEt.topology T)
    (O := Scheme.proEtaleConstantRing T A) (O' := Scheme.proEtaleConstantRing T B)
    (Scheme.proEtaleConstantRingMap (T := T) φ)
  let hE := Classical.choose_spec h
  let hrest := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec hE))
  exact Classical.choose hrest.2.2

/-- Termwise restriction of scalars `Res_T : D(B_T) ⥤ D(A_T)` (def-pc-sheaf-restrict-scalars),
localized to the unbounded derived categories; it is exact.
Source: Stacks Tag 07A6 (blueprint: def-sp-open-scalar-operations). -/
noncomputable def scalarRestriction {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    Scheme.proEtaleDerivedCategory T B ⥤ Scheme.proEtaleDerivedCategory T A :=
  (Scheme.proEtaleRingRestrictScalars
    (Scheme.proEtaleConstantRingMap (T := T) φ)).mapDerivedCategory

/-- The exact derived open extension `e_A = j_!^A`: the termwise extension by zero (left
adjoint of restriction to the open slice), localized to the unbounded derived categories;
its open adjunction `e_A ⊣ r_A` is `Scheme.proEtaleRingDerivedOpenAdjunction`.
Source: Stacks Tags 03DJ and 08FJ (blueprint: def-sp-open-scalar-operations). -/
noncomputable def openExtension {A : Type u} [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Scheme.proEtaleDerivedCategory U A ⥤ Scheme.proEtaleDerivedCategory X A :=
  Scheme.proEtaleRingDerivedOpenExtension j
    (Scheme.proEtaleConstantRing X A) (Scheme.proEtaleConstantRing U A)
    (Scheme.proEtaleConstantRingComparison j A)

end OpenScalarOperations

end AlgebraicGeometry.ProEtale
