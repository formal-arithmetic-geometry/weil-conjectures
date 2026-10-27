/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R5
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.TorAmplitude

/-! # Objectwise compact-support comparisons for constructible torsion coefficients -/

@[expose] public section

set_option autoImplicit false

universe u' u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A] [MonoidalPreadditive A]
  [SymmetricCategory A] [MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
  {FA : A → A → Type (u + 1)} {CA : A → Type (u + 1)}
  [∀ P Q, FunLike (FA P Q) (CA P) (CA Q)] [ConcreteCategory.{u + 1} A FA]
  [HasSmallSiteSheafify A]

/-- The compact-support projection formula when either factor is finite-Tor constructible.

Source: the current blueprint, sec-six-functors/sk-thm-sf-kunneth-relative,
proof steps (2) and (4), and the torsion projection formula sk-rem-sf-pf-done.
(blueprint: lem-sf-constructible-compact-support-projection).

Proof: factor f as an open immersion followed by a proper map. The open-immersion
projection formula identifies extension by zero of the tensor with the tensor of the
extension by zero. For the proper factor, check the projection comparison on geometric
fibres by proper base change. The constructible finite-Tor factor has a bounded flat
model on a finite constructible stratification. The explicit positive annihilators give
torsion stalks; the constant-complex projection formula on the proper fibre
commutes tensor with cohomology. Finite torsion cohomological dimension on each fibre
allows the other factor to be unbounded. Gluing along the open-closed triangles proves
the formula for either location of the constructible factor. Geometric stalk
conservativity proves invertibility. Compose with the open-immersion comparison. -/
theorem nonempty_iso_constructible_compact_support_projection
    {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f]
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A))
    (N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A))
    (h : (DerivedCategory.constructibleFiniteTor A X K ∧
        ∀ (n : ℤ) (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
          ∃ r : ℕ, 0 < r ∧ r • (𝟙 ((Scheme.pointSmallEtale s).sheafFiber.obj
            ((_root_.DerivedCategory.homologyFunctor _ n).obj K))) = 0) ∨
      (DerivedCategory.constructibleFiniteTor A Y N ∧
        ∀ (n : ℤ) (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ Y),
          ∃ r : ℕ, 0 < r ∧ r • (𝟙 ((Scheme.pointSmallEtale s).sheafFiber.obj
            ((_root_.DerivedCategory.homologyFunctor _ n).obj N))) = 0)) :
    Nonempty ((R(f)_![A]).obj
        (((derivedTensor A X).obj K).obj ((L((f)^*[A])).obj N)) ≅
      ((derivedTensor A Y).obj ((R(f)_![A]).obj K)).obj N) := by
  sorry

end AlgebraicGeometry.Etale
