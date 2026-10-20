/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.AlgebraicGeometry.IntrinsicDerivedOpenAdjunction
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
public import Sheaf.Paper.SfDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Finite-coefficient open-closed recollement triangles

Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-open-closed-triangle,
order 1834 (blueprint: def-weil-open-closed-recollement).

A recollement triangle is a connecting morphism completing the prescribed open counit
and closed unit to a distinguished triangle in the ordinary pro-etale derived category.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Scheme

/-- The canonical finite-coefficient derived inverse-image/direct-image adjunction.
It is induced from the section-normalized module adjunction by exact termwise pullback
and K-injective right derivation of direct image. Thus its unit is the specified closed
unit when the morphism is a closed immersion.
Source: blueprint order 1834; Stacks, Tags 03D3 and 07A6
(blueprint: def-weil-open-closed-recollement). -/
noncomputable def finiteRecollementDerivedAdjunction
    {Z X : Scheme.{u}} (i : Z ⟶ X) (A : Type u) [CommRing A] [Finite A] :
    sfIntrinsicDerivedPullback A i ⊣ proEtaleConstantDerivedDirectImage i A :=
  (sfIntrinsicConstantModuleAdjunction i A).mapDerivedCategoryRightDerivedAdjunction

/-- The data of an open-closed recollement triangle for the bounded constructible object
`K`: a connecting morphism, together with distinguishedness of the triangle whose first
map is the localized sheaf counit and whose second map is the closed derived unit.
The open adjunction is obtained by applying the sheaf adjunction termwise and localizing
at quasi-isomorphisms; its inverse image is canonically identified with open restriction.
No existence or constructibility-preservation assertion is included.
Source: Weil blueprint, sec-smooth-purity/sk-prop-sf-open-closed-triangle,
order 1834 (blueprint: def-weil-open-closed-recollement). -/
noncomputable def FiniteOpenClosedRecollementTriangle
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (hn : 1 ≤ n)
    {Z U X : Scheme.{u}} (i : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion i] [IsOpenImmersion j]
    (_hZ : ∀ z : Z, IsUnit (l : Z.presheaf.stalk z))
    (_hU : ∀ x : U, IsUnit (l : U.presheaf.stalk x))
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hij : Set.range j.base = (Set.range i.base)ᶜ)
    (K : proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n))
    (_hK : intrinsicFiniteTorsionConstructible l E n hn X K) : Type _ :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  { δ : (proEtaleConstantDerivedDirectImage i (Padic.coefficientExtensionRing l E n)).obj
        ((sfIntrinsicDerivedPullback (Padic.coefficientExtensionRing l E n) i).obj K) ⟶
      ((sfIntrinsicDerivedOpen (Padic.coefficientExtensionRing l E n) j).obj
        ((sfIntrinsicDerivedPullback (Padic.coefficientExtensionRing l E n) j).obj K))⟦(1 : ℤ)⟧ //
    Triangle.mk
      ((exceptionalOpenAdjunction j (Padic.coefficientExtensionRing l E n)).counit.app K)
      ((finiteRecollementDerivedAdjunction i
        (Padic.coefficientExtensionRing l E n)).unit.app K) δ ∈
      distTriang (proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n)) }

end AlgebraicGeometry.Scheme
