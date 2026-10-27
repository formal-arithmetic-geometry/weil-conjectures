/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R5
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

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

/-- Compact-support composition evaluated on an external finite-Tor constructible object.

Source: the current blueprint, sec-six-functors/sk-thm-sf-kunneth-relative,
proof step (1), and the compactification composition law.
(blueprint: lem-sf-constructible-external-composition).

Proof: compute each direct image with a compactification. Choose a compatible proper/open
compactification triangle for the projection and the second structure map. Move extension
by zero past the proper direct image in this triangle, compose the open extensions, and
compose the proper direct images. The resulting candidate computes the structure map of
the fibre product. Compare it to the chosen compactification by a common proper refinement.
Proper base change on the torsion homology of the external object makes this comparison
invertible; open extension is exact. The finite-Tor hypotheses allow bounded flat tensor
representatives locally, so the tensor and inverse images preserve this torsion domain.
The comparison is independent of the common refinement by its cocycle identity.
The explicit positive annihilators supply the torsion condition on both input stalks.
Evaluating the resulting composition comparison gives the asserted object isomorphism. -/
theorem nonempty_iso_constructible_external_composition
    {B X Y : Scheme.{u}} (f : X ⟶ B) (g : Y ⟶ B)
    [HasCompactification f] [HasCompactification g] [QuasiCompact f] [QuasiCompact g]
    [HasCompactification (pullback.toBase f g)]
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)}
    {M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    (hK : DerivedCategory.constructibleFiniteTor A X K)
    (hM : DerivedCategory.constructibleFiniteTor A Y M)
    (hTK : ∀ (n : ℤ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ X), ∃ N : ℕ, 0 < N ∧
        N • (𝟙 ((Scheme.pointSmallEtale s).sheafFiber.obj
          ((_root_.DerivedCategory.homologyFunctor _ n).obj K))) = 0)
    (hTM : ∀ (n : ℤ) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ Y), ∃ N : ℕ, 0 < N ∧
        N • (𝟙 ((Scheme.pointSmallEtale s).sheafFiber.obj
          ((_root_.DerivedCategory.homologyFunctor _ n).obj M))) = 0) :
    Nonempty ((R(pullback.toBase f g)_![A]).obj (externalProduct A f g K M) ≅
      (R(g)_![A]).obj
        ((R(pullback.snd f g)_![A]).obj (externalProduct A f g K M))) := by
  sorry

end AlgebraicGeometry.Etale
