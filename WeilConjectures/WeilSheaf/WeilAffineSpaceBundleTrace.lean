/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
import WeilConjectures.WeilSheaf.LowerShriekFunctoriality
import WeilConjectures.WeilSheaf.WeilAffineSpaceTrace
import WeilConjectures.WeilSheaf.LowerShriekOperations
import WeilConjectures.WeilSheaf.FourierInversion.UpperStar

/-!
# The compact-support trace for a trivial affine-space bundle on Weil complexes

For a trivial affine-space bundle `π : Y ⟶ X` of rank `n` (given by a cartesian square over the
standard affine space), the compact-support integral along `π` of a pullback is the Tate twist
`(-n)` followed by the shift `[-2n]`. This is the Thom isomorphism specialized to a trivial
bundle, as used in the computation of the Fourier convolution kernel.

## Implementation details

The statement is reduced to the standard affine-space trace by compact-support base change along
the isomorphism from `Y` to the standard affine space over `X` given by the universal property
of the cartesian square; only the standard trace calculation remains an input.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

/-- The compact-support integral of the pullback to a trivial rank-n affine bundle
is the rank Tate twist and cohomological shift. -/
theorem nonempty_iso_upperStar_comp_derivedLowerShriek_affineSpace_of_isPullback
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime]
    [Fact (ringChar k₀ ≠ l)] (n : Type u) [Fintype n] {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    (π : Y ⟶ X) (s : Y ⟶ AffineSpace n (Spec (CommRingCat.of k₀)))
    [π.IsOver (Spec (CommRingCat.of k₀))]
    (hπ : IsPullback π s (X ↘ Spec (CommRingCat.of k₀))
      (AffineSpace n (Spec (CommRingCat.of k₀)) ↘ Spec (CommRingCat.of k₀)))
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (upperStar π ⋙ derivedLowerShriek k₀ l π ≅
      tateTwist k₀ l X (-(Fintype.card n : ℤ)) ⋙
        shiftFunctor _ (-(2 * (Fintype.card n : ℤ)))) := by
  let A := AffineSpace n X
  let p : A ⟶ X := AffineSpace n X ↘ X
  let : A.Over (Spec (CommRingCat.of k₀)) :=
    ⟨p ≫ X ↘ Spec (CommRingCat.of k₀)⟩
  have : p.IsOver (Spec (CommRingCat.of k₀)) := ⟨rfl⟩
  let sq := (AffineSpace.isPullback_map (n := n) (X ↘ Spec (CommRingCat.of k₀))).flip
  let e : Y ≅ A := hπ.isoIsPullback _ _ sq
  have he : e.hom ≫ p = π := hπ.isoIsPullback_hom_fst _ _ sq
  have : e.hom.IsOver (Spec (CommRingCat.of k₀)) := ⟨by
    change e.hom ≫ (p ≫ X ↘ Spec (CommRingCat.of k₀)) = _
    rw [← Category.assoc, he, comp_over π]⟩
  have eSq : IsPullback e.hom π p (𝟙 X) :=
    IsPullback.of_horiz_isIso ⟨he.trans (Category.comp_id π).symm⟩
  obtain ⟨bc⟩ := nonempty_iso_derivedLowerShriek_upperStar (k₀ := k₀) (l := l)
    p (𝟙 X) π e.hom eSq
  obtain ⟨uid⟩ := nonempty_iso_upperStar_id (k₀ := k₀) (l := l) (X := X)
  obtain ⟨ucomp⟩ := nonempty_iso_upperStar_comp (k₀ := k₀) (l := l) e.hom p
  let ueq := upperStarCongrIso (k₀ := k₀) (l := l) he
  obtain ⟨tr⟩ := nonempty_iso_affineSpace_integral (k₀ := k₀) (l := l) n X
  let U := upperStar (k₀ := k₀) (l := l) p
  let D := derivedLowerShriek k₀ l p
  let Dπ := derivedLowerShriek k₀ l π
  have trans : U ⋙ D ≅ upperStar π ⋙ Dπ :=
    (Functor.rightUnitor (U ⋙ D)).symm ≪≫
      Functor.isoWhiskerLeft (U ⋙ D) uid.symm ≪≫
      Functor.isoWhiskerLeft U bc ≪≫
      (Functor.associator U (upperStar e.hom) Dπ).symm ≪≫
      Functor.isoWhiskerRight (ucomp.symm ≪≫ ueq) Dπ
  exact ⟨trans.symm ≪≫ tr⟩

end AlgebraicGeometry.WeilComplex
