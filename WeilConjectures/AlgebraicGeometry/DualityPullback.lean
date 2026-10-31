/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum
public import WeilConjectures.AlgebraicGeometry.DualityPullbackData
import WeilConjectures.AlgebraicGeometry.DualityPullbackSupportIndependence
import WeilConjectures.AlgebraicGeometry.DualityPullbackIdentity
import WeilConjectures.AlgebraicGeometry.DualityPullbackComposition
import WeilConjectures.AlgebraicGeometry.DualityPullbackSmooth

/-! # Coherent duality against pullback at finite coefficients

Source: literature/blueprint/latest/blueprint/sec-six-functors/sk-rem-sf-kv-formal/
cor-sf-duality-pullback.md and its proof (blueprint: cor-sf-duality-pullback).

The current source uses finite rings on the small etale site. Natural isomorphisms
are displayed through the fully faithful inclusion of the finite-Tor subcategory.
The identity and composition comparisons below are actual compactification maps and
their right-adjoint mates, not independently chosen comparison isomorphisms.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
variable (k : Type u) [Field k]

set_option maxHeartbeats 200000 in
-- Normalization transports the actual compactification-comparison functors.
set_option maxRecDepth 4000 in
/-- A coherent natural duality-pullback isomorphism and its smooth oriented form.
The finite coefficient datum is the existing six-operations package, on every map
in the separated finite-type setting. No nonfinite coefficient model is used.

Source: latest blueprint cor-sf-duality-pullback and its proof
(blueprint: cor-sf-duality-pullback).

Proof: construct the adjoint transform of canonical Verdier exchange using the
internal-Hom self-adjunctions and the two ordinary adjunctions. Its explicit Hom
formula is bidual transpose, ordinary adjunction, inverse Verdier exchange,
bidual transpose, and exceptional adjunction. Choose compatible compactification
coordinates using `ofComp`; the unbounded tower formula shows independence of
these coordinates and therefore proves normalization in every coordinate.
Apply the normalized identity and composition calculations with the actual unit
and compositor maps. For a smooth morphism, naturality and invertibility of the
canonical dualizing tensor map assemble functorial purity. Substitute the given
orientation and restrict the resulting comparison to the finite-Tor category. -/
theorem coherent_duality_pullback [IsAlgClosed k] [HasTateTwist Λ]
    [HasInvertibleExponent Λ (Spec (.of k))]
    (datum : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (aY : Y ⟶ Spec (.of k))
      [HasCompactification f] [QuasiCompact f] [IsSeparated f]
      [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
      [HasCompactification aY] [HasCompactification (f ≫ aY)],
      SixOperationsPackage Λ k f aY) :
    ∃ chi : FiniteDualityPullbackFamily Λ k,
      FiniteDualityPullbackNormalized Λ k chi ∧ FiniteDualityPullbackIdentity Λ k chi ∧
      FiniteDualityPullbackComposition Λ k chi ∧
      ∀ (C : OrientationComparisonData Λ) (_O : OrientationDatum Λ C)
        {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
        [IsSeparated aX] [LocallyOfFiniteType aX] [QuasiCompact aX] [HasCompactification aX]
        [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY] [HasCompactification aY]
        (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
        [HasCompactification f] (_hf : f ≫ aY = aX) (d : ℕ)
        [SmoothOfRelativeDimension d f],
        Nonempty ((DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).ι.op ⋙
            L((f)^*[ModuleCat.{u + 1} Λ]).op ⋙ verdierDual Λ aX ≅
          (DerivedCategory.constructibleFiniteTor (ModuleCat.{u + 1} Λ) Y).ι.op ⋙
            verdierDual Λ aY ⋙ L((f)^*[ModuleCat.{u + 1} Λ]) ⋙ twistShift Λ X d) := by
  let chi : FiniteDualityPullbackFamily Λ k := canonicalFiniteDualityPullbackFamily Λ k
  have hN : FiniteDualityPullbackNormalized Λ k chi :=
    canonicalFiniteDualityPullbackFamily_normalized Λ k
  have hI : FiniteDualityPullbackIdentity Λ k chi :=
    normalized_duality_pullback_identity Λ k datum chi hN
  have hC : FiniteDualityPullbackComposition Λ k chi :=
    normalized_duality_pullback_composition Λ k datum chi hN
  exact ⟨chi, hN, hI, hC, duality_pullback_smooth_orientation_core Λ k⟩

end AlgebraicGeometry.Etale
