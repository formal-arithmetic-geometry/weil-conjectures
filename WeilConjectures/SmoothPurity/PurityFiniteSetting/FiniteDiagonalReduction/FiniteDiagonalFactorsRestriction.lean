/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalOrientationRestrictionData
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalAlphaRestriction
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalVectorRestriction

/-! # Factors diagonal restriction
(blueprint: lem-pur-finite-diagonal-factors-restriction). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
open Etale.FiniteSmoothPurity

private theorem three_squares {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {A B C₀ D₀ : C} {A' B' C' D' : D}
    {a : A ⟶ B} {b : B ⟶ C₀} {c : C₀ ⟶ D₀}
    {a' : A' ⟶ B'} {b' : B' ⟶ C'} {c' : C' ⟶ D'}
    {r : F.obj A ⟶ A'} {s : F.obj B ⟶ B'}
    {n : F.obj C₀ ⟶ C'} {t : F.obj D₀ ⟶ D'}
    (ha : F.map a ≫ s = r ≫ a') (hb : F.map b ≫ n = s ≫ b')
    (hc : F.map c ≫ t = n ≫ c') :
    F.map (a ≫ b ≫ c) ≫ t = r ≫ a' ≫ b' ≫ c' := by
  simp only [Functor.map_comp, Category.assoc]
  rw [hc, reassoc_of% hb, reassoc_of% ha]

variable (P : PurityFiniteSetting.{u})
variable {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable [SmoothOfRelativeDimension d f]
variable (aY : Y ⟶ Spec (.of P.field.k))
variable [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]

/-- The three-factor diagonal assembly commutes with source and target open
restriction, without identifying it with the chosen orientation.
Source: latest orientation charts proof, Steps 1--4, and diagonal assembly proof
Steps 2--3. Proof: first base change the self-product section pair along U -> X,
then restrict its ambient space to U times_V U, an open neighbourhood of its
section. Exceptional base-change mate pasting gives the alpha square.
SectionRestriction.coherence gives the normalized delta square for these two
operations, with the actual associated-graded cone and augmentation section.
Vector integration base change and the ordinary vector orientation normalization
give the beta square. The coefficient comparison is the specified projective-line
transport. Compose the three squares; cancel the intermediate source and normal
comparison isomorphisms. The remaining outer square is the displayed equation.
The same argument includes the empty open and the empty rank-zero tensor.
(blueprint: lem-pur-finite-diagonal-factors-restriction). -/
theorem diagonalFactorsRestriction
    (U : X.affineOpens) (V : Y.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1)
    [SmoothOfRelativeDimension d (f.resLE V.1 U.1 hUV)] :
    letI : IsAffine U.1.toScheme := U.2
    letI : IsAffine V.1.toScheme := V.2
    let h := f.resLE V.1 U.1 hUV
    let R := (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
      U.1.ι).leftDerivedFunctor
    R.map ((P.chartDiagonalAlpha d f aY).inv ≫
        (P.chartDiagonalDelta d f aY).hom ≫ (vectorFactor P d f aY).hom) ≫
        (affineTateRestriction P f aY d U).hom =
      (affineDualizingRestriction P f aY U V hUV).hom ≫
        (P.chartDiagonalAlpha d h (V.1.ι ≫ aY)).inv ≫
        (P.chartDiagonalDelta d h (V.1.ι ≫ aY)).hom ≫
        (vectorFactor P d h (V.1.ι ≫ aY)).hom := by
  let := P.noetherian aY
  let := P.noetherian (f ≫ aY)
  dsimp only
  have ha := alpha_square d f U V hUV P aY
  have hd := RestrictionGeometry.delta_square d f U V hUV P aY
  have hv := vector_square d f U V hUV P aY
  exact three_squares ha hd hv

end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
