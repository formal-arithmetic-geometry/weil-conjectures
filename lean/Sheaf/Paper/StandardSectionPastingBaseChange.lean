/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module

public import Sheaf.Paper.PurityDiagonalSectionPasting
public import Sheaf.Paper.PurityDncComparisons

/-! # Base change of the ordinary standard section-pasting map

Source: composition coherence Step 1, compatible-DNC-charts proof Step 8.
(blueprint: lem-pur-standard-section-pasting-base-change).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The ordinary etale geometric part of standard section-pasting base change.
No comparison between sites or pro-etale tensor constraint enters this equation.
Source: composition coherence Step 1; compatible-DNC-charts proof Step 8
(blueprint: lem-pur-standard-section-pasting-base-change).

Proof: write nu as the zero-section pullback of sigma for the ordered tower
A^(d+e)_B -> A^e_B -> B, preceded by the inverse smooth base-change map for
its first block and the pullback-composition map for its second block. Base
change the tower along b, using the affine-space Cartesian squares. Their
zero sections commute with the affine-space maps, as do both block projections.
The sigma base-change identity of dualizing_sigma_cocycle_locality identifies
pullback of sigma followed by the total dualizing base-change mate with the
tensor of the two factor mates followed by the base-changed sigma. Pull that
identity along the new total zero section. Naturality and composition of the
derived pullback tensor constraint move it before the two factor comparisons.
Pasting Cartesian base-change mates identifies the first factor with the
sectionBaseChange for rank d; coherence of pullback composition identifies the
second with sectionBaseChange for rank e. The total mate is sectionBaseChange
for rank d+e. These substitutions yield the displayed equation, with no
orientation used. All squares and mates exist for empty schemes and empty
coordinate blocks, so the argument includes rank zero. -/
theorem standardSectionPasting_baseChange (P : PurityFiniteSetting.{u})
    {B' B : Scheme.{u}} [IsAffine B'] [IsAffine B]
    (d e : ℕ) (b : B' ⟶ B) [Etale b]
    (aB : B ⟶ Spec (.of P.field.k)) [LocallyOfFiniteType aB] [QuasiCompact aB]
    [LocallyOfFiniteType b] [QuasiCompact b] :
    letI := P.noetherian aB
    letI := P.noetherian (b ≫ aB)
    letI := P.comparedExponent (𝟙 (Spec (.of P.field.k)))
    let bc := fun r : ℕ ↦
      letI := Dnc.invertibleExponent P (DiagonalPasting.pr r B ≫ aB)
      letI := Dnc.compactifiable P (DiagonalPasting.pr r B) aB
      letI := Dnc.compactifiable P (DiagonalPasting.pr r B') (b ≫ aB)
      letI := DiagonalPasting.affineDimension r B
      Dnc.sectionBaseChange P.Coefficient r (DiagonalPasting.pr r B)
        (AffineSpace.isPullback_map b) (DiagonalPasting.zero r B)
        (DiagonalPasting.zero r B') (AffineSpace.zeroSection_comp_map b)
    (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) b).leftDerivedFunctor.mapIso
        (DiagonalPasting.nu P.Coefficient P d e B aB) ≪≫ bc (d + e) =
      Etale.leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} P.Coefficient) b
        (DiagonalPasting.zeroInvariant P.Coefficient P d B)
        (DiagonalPasting.zeroInvariant P.Coefficient P e B) ≪≫
      DiagonalPasting.tensorComparison P.Coefficient P (bc d) (bc e) ≪≫
        DiagonalPasting.nu P.Coefficient P d e B' (b ≫ aB) := by sorry

end WeilConjectures.PurityFiniteSetting
