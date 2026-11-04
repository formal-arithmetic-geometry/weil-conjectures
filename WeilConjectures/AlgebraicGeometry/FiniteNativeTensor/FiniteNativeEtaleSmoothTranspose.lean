/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteNativeTensor.FiniteNativeEtaleProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality
import all WeilConjectures.AlgebraicGeometry.EtaleSmoothDualityTensor

/-! # The smooth etale transpose for a supplied compactification

The chosen compactification adjunction is the published exceptional adjunction
transported by its canonical compact-support isomorphism.
(blueprint: lem-pur-finite-native-etale-smooth-transpose).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.ProEtale.FiniteNativeTensor

/-- Smooth duality identifies the actual counit transpose for every supplied
compactification. Source: `Etale.exists_dualizingComplex_iso_and_tensor` and the
counit compatibility of compactification comparison.
(blueprint: lem-pur-finite-native-etale-smooth-transpose).

Proof: use the smooth tensor theorem for the published exceptional adjunction.
The unit tensor map is its ambient transpose. The compactification comparison
preserves projection, and the two compactification counit factors cancel, so this
ambient transpose equals that for the supplied compactification. -/
theorem canonicalEtaleSmoothTranspose_isIso (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    [HasInvertibleExponent A X] (c : Compactification f)
    (df : ℕ) [SmoothOfRelativeDimension df f]
    (K : Etale.DerivedCategoryModule A Y) :
    let : HasCompactification f := c.hasCompactification
    let G := Etale.rightDerivedUpperShriek A f
    let adj := (Etale.rightDerivedUpperShriekAdjunction A f).ofNatIsoLeft
      (Etale.rightDerivedLowerShriekIso A c).symm
    letI := canonicalEtaleProjection_isIso A c (G.obj (𝟙_ _)) K
    IsIso (adj.homEquiv _ _
      (inv (canonicalEtaleProjection A c (G.obj (𝟙_ _)) K) ≫
        (adj.counit.app (𝟙_ _) ▷ K) ≫ (λ_ K).hom)) := by
  let : HasCompactification f := c.hasCompactification
  obtain ⟨_, _, _, _, hθ⟩ := Etale.exists_dualizingComplex_iso_and_tensor A f df
  have ht := hθ K
  rw [← Etale.ambientTensorMap_eq A f K,
    ← Etale.ambientTensorMap_compactification A f c] at ht
  exact ht

end AlgebraicGeometry.ProEtale.FiniteNativeTensor
