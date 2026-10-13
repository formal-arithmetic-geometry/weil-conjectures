/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.FourierInversion.ArtinSchreier
public import WeilConjectures.WeilSheaf.FourierInversion.OtherSections
public import WeilConjectures.WeilSheaf.FourierInversion.TensorLisse
public import WeilConjectures.WeilSheaf.FourierInversion.UpperStar
public import WeilConjectures.WeilSheaf.FourierInversion.Vanishing

/-!
# Fourier inversion: the delta kernel on a trivial line bundle

`Rπ₀!(ℒ_ψ(h s) ⊗ π^* P) ≅ Ri₀!((i^* P)(-1)[-2])` for the trivial line bundle `π` with fibre
coordinate `s` and the zero locus `i` of a function `h` (blueprint `lem-fd-convolution-kernel`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **The delta kernel on a trivial line bundle** (the relative form of blueprint
`lem-fd-convolution-kernel`, `sk-prop-convolution-kernel`). Let `h` be a function on a
`k₀`-scheme `X` (as a morphism `X ⟶ 𝔸¹`), with zero locus `i : Z ⟶ X` (the base change of
the zero section along `h`), let `π : Y ≅ X ×_{k₀} 𝔸¹ ⟶ X` be the trivial line bundle with
fibre coordinate `s`, and let `ψ` be nontrivial. Then

`Rπ₀!(ℒ_ψ(h s) ⊗ π^* P) ≅ Ri₀!((i^* P)(-1)[-2])`

naturally in the Weil complex `P` on `X`. Over the open set `h ≠ 0` the left side vanishes by
`AlgebraicGeometry.WeilComplex.isZero_derivedLowerShriek_tensorLisse_artinSchreierOf_upperStar`
and base change; over `Z` the kernel is `ℒ_{ψ,0} ≅ ℚ̄_ℓ` and the Thom isomorphism
`AlgebraicGeometry.WeilComplex.nonempty_iso_upperStar_comp_derivedLowerShriek_of_isPullback`
applies; the recollement
`AlgebraicGeometry.WeilComplex.exists_isIso_app_of_isZero_upperStar` glues the two. -/
theorem WeilComplex.nonempty_iso_derivedLowerShriek_tensorLisse_artinSchreierOf_mul
    (ψ : AddChar k₀ (PadicAlgCl l)) (hψ : ψ ≠ 1) {X Y Z : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k₀))] [Y.Over (Spec (CommRingCat.of k₀))]
    [Z.Over (Spec (CommRingCat.of k₀))] (h : X ⟶ affineLine k₀)
    [h.IsOver (Spec (CommRingCat.of k₀))] (π : Y ⟶ X) (s : Y ⟶ affineLine k₀)
    [π.IsOver (Spec (CommRingCat.of k₀))]
    (hπ : IsPullback π s (X ↘ Spec (CommRingCat.of k₀))
      (affineLine k₀ ↘ Spec (CommRingCat.of k₀)))
    (i : Z ⟶ X) [i.IsOver (Spec (CommRingCat.of k₀))]
    (hi : IsPullback (Z ↘ Spec (CommRingCat.of k₀)) i
      (AffineSpace.zeroSection PUnit.{u + 1} (Spec (CommRingCat.of k₀))) h)
    [IsSeparated π] [LocallyOfFiniteType π] [QuasiCompact π]
    [IsSeparated i] [LocallyOfFiniteType i] [QuasiCompact i]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))] :
    Nonempty (WeilComplex.upperStar π ⋙
        WeilComplex.tensorLisse (artinSchreierOf ψ
          (π.appTop (h.appTop (AffineSpace.coord _ PUnit.unit)) *
            s.appTop (AffineSpace.coord _ PUnit.unit))) (isLisse_artinSchreierOf ψ _) ⋙
        WeilComplex.derivedLowerShriek k₀ l π ≅
      WeilComplex.upperStar i ⋙ WeilComplex.tateTwist k₀ l Z (-1) ⋙
        shiftFunctor _ (-2 : ℤ) ⋙ WeilComplex.derivedLowerShriek k₀ l i) :=
  sorry


end AlgebraicGeometry
