/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveAffineTargetNoetherian
import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveAffineTargetApproximation

/-!
# Affineness of a finite surjective image

## References

* Stacks Project, Tag 01ZT.
-/

@[expose] public section

universe u

open CategoryTheory
namespace AlgebraicGeometry

/-- If a finite morphism is surjective and its source is affine, then its target is affine.
(Stacks, Tag 01ZT.) -/
theorem isAffine_of_isFinite_surjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsFinite f] [Surjective f] [IsAffine X] : IsAffine Y := by
  obtain ⟨a⟩ := exists_noetherian_affine_factor f
  have : IsNoetherian a.Z := a.noetherian_Z
  have : IsFinite a.g := a.finite_g
  have : Surjective a.g := a.surjective_g
  have : IsAffine a.W := a.affine_W
  have : IsAffine a.Z := isAffine_of_isFinite_surjective_of_isNoetherian a.g
  have : IsAffineHom a.q := a.affine_q
  exact isAffine_of_isAffineHom a.q

end AlgebraicGeometry
