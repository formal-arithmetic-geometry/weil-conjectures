/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility

/-!
# Canonical coefficient comparisons for direct images and internal Hom

Source: the adopted `AlgebraicGeometry.coefficientChangeCompatibility` docstring and fields.
The latest blueprint `lem-fix-operation-reduction` supplies the route on its narrower stages.
-/

@[expose] public section
set_option autoImplicit false
universe u

-- Normalize quotient coefficient instances as in IntegralCoefficients.
attribute [local instance 2000] CommRing.toRing
open CategoryTheory Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.CoefficientChange

set_option hygiene false in
local notation "DE(" X ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} A))
set_option hygiene false in
local notation "DP(" X ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))

/-- The fixed left adjoint of derived coefficient restriction on the small étale site. -/
noncomputable abbrev etaleExtension {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) : DE(X, A) ⥤ DE(X, B) :=
  ProEtale.pbcFixedScalarExtension X.smallEtaleTopology φ

/-- The fixed left adjoint of derived coefficient restriction on the pro-étale site. -/
noncomputable abbrev proExtension {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) : DP(X, A) ⥤ DP(X, B) :=
  ProEtale.pbcFixedScalarExtension (Scheme.ProEt.topology X) φ

/-- The principal quotient coefficient map. -/
abbrev quotient (A : Type (u + 1)) [CommRing A] (a : A) (n : ℕ) :=
  Ideal.Quotient.mk (Ideal.span {a} ^ n)

/-- Compact support, with coefficient instances fixed at a generic ring. -/
noncomputable abbrev etaleCompact (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] : DE(X, A) ⥤ DE(Y, A) :=
  Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f

/-- Compact support for a specified compactification, with generic coefficient instances. -/
noncomputable abbrev proCompact (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) : DP(X, A) ⥤ DP(Y, A) :=
  ProEtale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c

/-- Object comparisons for the canonical left adjoint. The input reductions and their
universal arrows are fixed, so no choice of an arbitrary reduction occurs here. -/
structure OperationComparisons : Prop where
  etaleDirect {A : Type (u + 1)} [CommRing A] {a : A}
    (ha : a ∈ nonZeroDivisors A) (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) (K : DE(X, A)) :
    Nonempty ((etaleExtension (quotient A a n) Y).obj
      (R(Etale.lowerStar (ModuleCat.{u + 1} A) f).obj K) ≅
      R(Etale.lowerStar (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n)) f).obj
        ((etaleExtension (quotient A a n) X).obj K))
  proDirect {A : Type (u + 1)} [CommRing A] {a : A}
    (ha : a ∈ nonZeroDivisors A) (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y) (K : DP(X, A)) :
    Nonempty ((proExtension (quotient A a n) Y).obj
      (R(ProEtale.lowerStar (ModuleCat.{u + 1} A) f).obj K) ≅
      R(ProEtale.lowerStar (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n)) f).obj
        ((proExtension (quotient A a n) X).obj K))
  etaleExceptional {A : Type (u + 1)} [CommRing A] {a : A}
    (ha : a ∈ nonZeroDivisors A) (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f]
    [(Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).IsLeftAdjoint]
    [(Etale.rightDerivedLowerShriek
      (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n)) f).IsLeftAdjoint] (L : DE(Y, A)) :
    Nonempty ((etaleExtension (quotient A a n) X).obj
      ((Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).rightAdjoint.obj L) ≅
      (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n))
      f).rightAdjoint.obj ((etaleExtension (quotient A a n) Y).obj L))
  proExceptional {A : Type (u + 1)} [CommRing A] {a : A}
    (ha : a ∈ nonZeroDivisors A) (n : ℕ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f]
    [(Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).IsLeftAdjoint]
    [(Etale.rightDerivedLowerShriek
      (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n)) f).IsLeftAdjoint] (L : DP(Y, A)) :
    Nonempty ((proExtension (quotient A a n) X).obj
      ((R(ProEtale.comparisonLowerStar (ModuleCat.{u + 1} A) Y) ⋙
        (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} A) f).rightAdjoint ⋙
        D(ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) X)).obj L) ≅
      (R(ProEtale.comparisonLowerStar (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n)) Y) ⋙
        (Etale.rightDerivedLowerShriek (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n))
      f).rightAdjoint ⋙
        D(ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n)) X)).obj
          ((proExtension (quotient A a n) Y).obj L))
  etaleHom {A : Type (u + 1)} [CommRing A] {a : A}
    (ha : a ∈ nonZeroDivisors A) (n : ℕ) (X : Scheme.{u}) (K L : DE(X, A)) :
    Nonempty ((etaleExtension (quotient A a n) X).obj
      (((Etale.derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj L) ≅
      ((Etale.derivedHom (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n)) X).obj
        (op ((etaleExtension (quotient A a n) X).obj K))).obj
          ((etaleExtension (quotient A a n) X).obj L))
  proHom {A : Type (u + 1)} [CommRing A] {a : A}
    (ha : a ∈ nonZeroDivisors A) (n : ℕ) (X : Scheme.{u}) (K L : DP(X, A)) :
    Nonempty ((proExtension (quotient A a n) X).obj
      (((ProEtale.derivedHom (ModuleCat.{u + 1} A) X).obj (op K)).obj L) ≅
      ((ProEtale.derivedHom (ModuleCat.{u + 1} (A ⧸ Ideal.span {a} ^ n)) X).obj
        (op ((proExtension (quotient A a n) X).obj K))).obj
          ((proExtension (quotient A a n) X).obj L))
  etaleFiniteCompact {A : Type (u + 1)} [CommRing A] {a : A}
    (ha : a ∈ nonZeroDivisors A) {m n : ℕ} (h : m ≤ n)
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (K : DE(X, A ⧸ Ideal.span {a} ^ n))
    (hK : Etale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1}
      (A ⧸ Ideal.span {a} ^ n)) X K) :
    Nonempty ((etaleExtension (Ideal.Quotient.factor (Ideal.pow_le_pow_right h)) Y).obj
      ((etaleCompact (A ⧸ Ideal.span {a} ^ n) f).obj K) ≅
      (etaleCompact (A ⧸ Ideal.span {a} ^ m) f).obj
        ((etaleExtension (Ideal.Quotient.factor (Ideal.pow_le_pow_right h)) X).obj K))
  proFiniteCompact {A : Type (u + 1)} [CommRing A] {a : A}
    (ha : a ∈ nonZeroDivisors A) {m n : ℕ} (h : m ≤ n)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DP(X, A ⧸ Ideal.span {a} ^ n))
    (hK : ProEtale.DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1}
      (A ⧸ Ideal.span {a} ^ n)) X K) :
    Nonempty ((proExtension (Ideal.Quotient.factor (Ideal.pow_le_pow_right h)) Y).obj
      ((proCompact (A ⧸ Ideal.span {a} ^ n) c).obj K) ≅
      (proCompact (A ⧸ Ideal.span {a} ^ m) c).obj
        ((proExtension (Ideal.Quotient.factor (Ideal.pow_le_pow_right h)) X).obj K))

/-- Canonical object comparisons for principal and finite quotient reduction.
Source: the adopted `AlgebraicGeometry.coefficientChangeCompatibility` docstring and fields;
the latest blueprint `lem-fix-operation-reduction` proof paragraphs on direct image,
compact support, internal Hom and exceptional inverse image
(blueprint: lem-coefficient-operation-comparisons).

Proof: a principal quotient by a nonzerodivisor is represented by the two-term free
Koszul complex. Compute scalar extension on a K-flat resolution. Each linear derived
operation carries the multiplication map by the indicated power to the corresponding
multiplication map. Applying it to the Koszul triangle identifies scalar extension
before and after ordinary direct image, compact support, and internal Hom. Construct
these comparisons over the quotient ring on the scalar-extended representatives;
the underlying cone comparison proves they are isomorphisms. For compact support,
factor through an open immersion and a proper map: open extension is exact and
commutes with termwise scalar extension; on the proper factor use the preceding
coefficient comparison. The induced comparison is independent of compactification.
For exceptional inverse image transpose the compact-support comparison with the
specified adjunctions. The finite free resolution of the coefficient quotient makes
that mate invertible. The pro-étale exceptional functor is the specified composite
of comparison pushforward, the étale exceptional functor, and comparison pullback;
paste their coefficient comparisons.

Between finite quotients, choose bounded flat models on constructible finite-Tor
inputs; the compact-support comparison is computed by the same proper/open
factorization. The finite-quotient internal-Hom comparison is proved separately in
the consuming module from dualizability and derived strong monoidality; it is not
part of this statement. -/
theorem operationComparisons : OperationComparisons.{u} := by
  sorry

end AlgebraicGeometry.CoefficientChange
