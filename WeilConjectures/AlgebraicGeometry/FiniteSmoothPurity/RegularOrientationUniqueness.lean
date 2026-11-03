/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSectionIntegratedSpecialization

/-! # Uniqueness of the specified diagonal/Rees orientation

Source: sk-thm-regular.proof.md, Step 4(ii)--(iii): normalized orientations can
be compared by their actual diagonal, specialization and bundle factors.
(blueprint: lem-pur-regular-orientation-uniqueness).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity

/-- The published Rees normalization determines the smooth orientation uniquely.

Proof: the two normalized family comparisons are equal by uniqueness of the
comparison normalized at one. Their normal-cone pullback squares are proofs of
the same proposition. Thus the two orientation equations have identical left
sides and identical final factors. Bundle integration adjoint and normal-section
exchange are isomorphisms, so cancel them to identify the orientation morphisms.
Equality of isomorphisms follows from equality of their forward morphisms.
The proof cancels the explicit normalized family and integration factors.
Source: sk-thm-regular.proof.md, Step 4(ii)--(iii)
(blueprint: lem-pur-regular-orientation-uniqueness). -/
theorem regular_normalized_orientation_unique
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Y) [HasCompactification f] [QuasiCompact f] [IsSeparated f]
    (d : ℕ) [SmoothOfRelativeDimension d f]
    (G : FiniteRingSectionDeformation.Geometry d
      (pullback.fst f f) (pullback.diagonal f))
    (hX : IsUnit (N : Γ(X, ⊤)))
    (α β : dualizingComplex A f ≅ line A N hA X d)
    (hα : OrientationNormalized A N hN hA f d G hX α)
    (hβ : OrientationNormalized A N hN hA f d G hX β) : α = β := by
  let := G
  obtain ⟨κ, hκ, sq, ha⟩ := hα
  obtain ⟨κ', hκ', sq', hb⟩ := hβ
  have hk : κ' = κ :=
    (FiniteRingSectionDeformation.existsUnique_normalized N hN A hA hX d
      (pullback.fst f f) (pullback.diagonal f) (pullback.diagonal_fst f)).unique hκ' hκ
  subst κ'
  have := normalSectionMap_isIso A d (pullback.fst f f) (pullback.diagonal f)
    (pullback.diagonal_fst f) sq N hN hA hX
  have := (FiniteRingSectionDeformation.bundleAdjoint_isIso
    N hN A hA X hX d (ConormalGradedAlgebra.piece (pullback.diagonal f) 1)).2
  apply Iso.ext
  exact (cancel_mono
    (FiniteRingSectionDeformation.bundleSectionAdjoint N hN A hA X hX d
      (ConormalGradedAlgebra.piece (pullback.diagonal f) 1) ≫
        normalSectionMap A d (pullback.fst f f) (pullback.diagonal f)
          (pullback.diagonal_fst f) sq)).mp (ha.symm.trans hb)

end AlgebraicGeometry.Etale.FiniteSmoothPurity
