/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineAlgebraKInjectiveCounitCompatibility
import WeilConjectures.AlgebraicGeometry.AffineAlgebraCanonicalComparisonIdentification

/-! # Invertibility of the canonical affine direct-image homology comparison

Source: Stacks Project, Tags 0AVW and 08D4.
-/

@[expose] public section
universe v
open CategoryTheory
namespace AlgebraicGeometry

/-- The canonical comparison, rather than an arbitrary isomorphism between its
source and target, is invertible for a K-injective complex with quasi-coherent
cohomology under an affine morphism (Stacks, Tags 0AVW and 08D4). -/
theorem affineAlgebraCounitHomologyComparison_isIso
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    (P : SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)) ⥤
      SheafOfModules.{v} (moduleRings X.toRingedSpace))
    [P.Additive] [Limits.PreservesFiniteLimits P] [Limits.PreservesFiniteColimits P]
    (a : P ⊣ RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f))
    (I : CochainComplex (SheafOfModules.{v} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] (hI : ∀ n : ℤ, (I.homology n).IsQuasicoherent) (n : ℤ) :
    IsIso (affineAlgebraCounitHomologyComparison f P a I n) := by
  obtain ⟨e, he⟩ := affine_algebra_kinjective_canonical_comparison_identification
    f P a I hI n
  rw [← he]
  infer_instance

end AlgebraicGeometry
