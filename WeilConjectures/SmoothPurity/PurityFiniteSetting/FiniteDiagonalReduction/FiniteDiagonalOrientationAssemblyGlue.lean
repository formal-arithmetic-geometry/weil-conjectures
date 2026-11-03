/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteDiagonalReduction.FiniteDiagonalReductionComparisons
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Model.ModelOrientationTateDetection

/-! # Global descent for finite diagonal orientation maps

(blueprint: lem-pur-finite-diagonal-orientation-assembly-glue).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
open Etale.FiniteSmoothPurity

variable (P : PurityFiniteSetting.{u})
variable {X Y : Scheme.{u}} (d : ℕ) (f : X ⟶ Y)
variable [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
variable [SmoothOfRelativeDimension d f]
variable (aY : Y ⟶ Spec (.of P.field.k))
variable [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]

/-- Equality of the two finite diagonal maps is detected on a jointly surjective
open cover. This is the degree-zero descent step after cancelling the common Tate
shift. Source: blueprint/latest, thm-pur-finite-reduction-of-purity, proof Step 4;
lem-pur-degree-zero-derived-map-gluing.
Proof: shift the common Tate target by the negative even shift, use the canonical
single-complex identifications on the degree-zero coefficient sheaf, and apply the
restriction equality test in the degree-zero derived-map gluing theorem. Transport
back across the shift. The empty scheme is included through the empty-cover clause.
This helper is strictly an equality-detection statement: it constructs no local
orientation and contains no chart or DNC calculation.
(blueprint: lem-pur-finite-diagonal-orientation-assembly-glue). -/
theorem diagonalOrientationAssembly_of_affineLocal
    {I : Type u} (U : I → X.Opens) (hU : iSup U = ⊤)
    (h : ∀ i,
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) (U i).ι).mapDerivedCategory.map
          (P.diagonalDualizingObject d f aY).hom =
        (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) (U i).ι).mapDerivedCategory.map
          ((P.chartDiagonalAlpha d f aY).inv ≫
            (P.chartDiagonalDelta d f aY).hom ≫ (vectorFactor P d f aY).hom)) :
    (P.diagonalDualizingObject d f aY).hom =
      (P.chartDiagonalAlpha d f aY).inv ≫ (P.chartDiagonalDelta d f aY).hom ≫
        (vectorFactor P d f aY).hom := by
  let a := P.diagonalDualizingObject d f aY
  let b := (P.chartDiagonalAlpha d f aY).symm ≪≫
    P.chartDiagonalDelta d f aY ≪≫ vectorFactor P d f aY
  have hab : a.symm ≪≫ a = a.symm ≪≫ b := by
    apply (model_orientation_tate_detection P X (f ≫ aY) d).2.2 I U hU
    funext i
    apply Iso.ext
    simp only [Functor.mapIso_hom, Iso.trans_hom, Iso.symm_hom, Functor.map_comp]
    exact congrArg (fun z ↦
      (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient)
        (U i).ι).mapDerivedCategory.map a.inv ≫ z) (h i)
  have he : a.hom = b.hom := by
    apply (cancel_epi a.inv).1
    exact congrArg Iso.hom hab
  exact he

end WeilConjectures.PurityFiniteSetting.FiniteDiagonalReduction
