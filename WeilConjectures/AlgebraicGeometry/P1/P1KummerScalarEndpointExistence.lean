/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.P1.P1KummerScalarEndpoints
import all WeilConjectures.AlgebraicGeometry.SupportedKummerScalarMaps
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
import all WeilConjectures.SixFunctors.BaseChange.RestrictScalars
import WeilConjectures.AlgebraicGeometry.SupportedKummerScalarDerived
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerScalarSupplement
import WeilConjectures.CategoryTheory.FlatScalarUnit
import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement
import WeilConjectures.CategoryTheory.ExactRightDerivedAdjointKFlatRepresentative
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseRightDerived
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfShape
import WeilConjectures.AlgebraicGeometry.FiniteOrdinaryScalarUnit
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.SixFunctors.Finite.Stalk
import Mathlib.CategoryTheory.Sites.Adjunction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.AlgebraicGeometry.Supported.SupportedKummerRootScalarUnit
import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroAdjoint

/-! # Existence of normalized ordinary finite scalar endpoints

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts: coefficient images of Kummer classes
(blueprint: lem-sp-p1-kummer-scalar-endpoint-existence).
-/

@[expose] public section

set_option autoImplicit false
universe u

namespace AlgebraicGeometry.Etale

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify

private theorem derivedInsertion_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u})
    {F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)}
    (η : F ⟶ (Sheaf.restrictScalars T.smallEtaleTopology φ).obj G)
    (hη : SupportedDerivedScalarUnit φ T F G η) :
    IsIso (p1KummerDerivedInsertion φ T η) := by
  unfold p1KummerDerivedInsertion
  unfold SupportedDerivedScalarUnit at hη
  exact SheafExactDegreeZero.isIso_scalarAdjointInsertion T.smallEtaleTopology φ η hη

/-- Normalized unit and Tate-line endpoints exist for every finite coefficient-ring map.
The record fixes ordinary insertions on constants and pure-root generators, and fixes the
homomorphisms of its derived isomorphisms as the specified adjunction transposes.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts: coefficient images of Kummer classes
(blueprint: lem-sp-p1-kummer-scalar-endpoint-existence).

Proof steps:
1. Use the constant-sheaf adjunction's normalized coefficient map and its formula on
   every constant generator. Specialize the supported constant scalar-unit theorem to
   the identity immersion to obtain its unbounded derived universal property.
2. The normalized root scalar-unit theorem gives the Tate insertion directly for the
   arbitrary map `φ`, its pure-root formula, and its unbounded derived universal property.
   This uses flatness of the source Tate line, not flatness of the coefficient map.
3. Apply the exact adjoint-insertion criterion to both universal maps. Their `asIso`
   isomorphisms have exactly the required homomorphisms, so the generator formulas and
   definitional transpose equalities fill the endpoint record. This includes empty
   schemes and zero coefficient rings. -/
theorem p1KummerScalarEndpointExistence
    (T : Scheme.{u}) (N : ℕ) (hN : 0 < N) (hT : IsUnit (N : Γ(T, ⊤)))
    (A B : Type (u + 1)) [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (hA : (N : A) = 0) (hB : (N : B) = 0) :
    Nonempty (P1KummerScalarEndpoints φ N hA hB T) := by
  classical
  let η := normalizedConstantMap φ T
  have hη := normalizedConstantMap_apply φ T
  have hu := (supported_kummer_scalar_derived_units T A B φ (𝟙 T) η η hη hη).1
  obtain ⟨θ, hθ, hv⟩ := supported_kummer_root_scalar_unit φ T N hN hA hB hT
  have := derivedInsertion_isIso φ T η hu
  have := derivedInsertion_isIso φ T θ hv
  exact ⟨{
    unitInsertion := η
    lineInsertion := θ
    unit_normalization := hη
    line_normalization := hθ
    unitIso := asIso (p1KummerDerivedInsertion φ T η)
    lineIso := asIso (p1KummerDerivedInsertion φ T θ)
    unit_derived := rfl
    line_derived := rfl }⟩

end AlgebraicGeometry.Etale
