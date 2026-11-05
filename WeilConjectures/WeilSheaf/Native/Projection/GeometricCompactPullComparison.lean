/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.PoincareDuality.ProjectionFormulaOpenImmersion

/-! # Pullback composition before choosing a geometric compactification -/

@[expose] public noncomputable section

universe u

open CategoryTheory MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local instance 2000] MonoidalCategory.toMonoidalCategoryStruct

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (l : ℕ) [Fact l.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {f : X ⟶ Y} (c : Compactification f.left)

/-- The bounded pullback compositor with its ambient components. -/
def compactProjectionGeometricPullIso :
    boundedConstructibleUpperStar Λ l c.overG ⋙
      boundedConstructibleUpperStar Λ l c.overI ≅ boundedConstructibleUpperStar Λ l f :=
  (eqToIso (congrArg (boundedConstructibleUpperStar Λ l) c.overI_overG.symm) ≪≫
    boundedConstructibleUpperStarComp Λ l c.overI c.overG).symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The geometric exceptional projection factors through the canonical pullback compositor. -/
lemma compactProjectionGeometricPullIso_projection_eq
    (ε : boundedConstructibleUpperStar (Profinite.padicAlgClRingObj l) l c.overG ⋙
      boundedConstructibleUpperStar _ l c.overI ≅ boundedConstructibleUpperStar _ l f)
    (hε : ε = (eqToIso (congrArg (boundedConstructibleUpperStar _ l)
      c.overI_overG.symm) ≪≫ boundedConstructibleUpperStarComp _ l c.overI c.overG).symm)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj l⟧)
    (B : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj l⟧) :
    ObjectProperty.homMk
        (X := (boundedConstructibleLowerShriekOfCompactification l c).obj K ⊗ B)
        (Y := (boundedConstructibleLowerShriekOfCompactification l c).obj
          (K ⊗ (boundedConstructibleUpperStar _ l f).obj B))
        (exceptionalProjectionMorphismOfCompactification _ c K.obj B.obj) =
      (boundedConstructibleUpperStarLowerStarAdjunction l c.overG).projectionMorphism
          ((boundedConstructibleOpenImmersionLowerShriek _ l c.overI).obj K) B ≫
        (boundedConstructibleLowerStar l c.overG).map
          (inv ((boundedConstructibleOpenImmersionLowerShriekUpperStarAdjunction _ l
              c.overI).projectionComparison K
              ((boundedConstructibleUpperStar _ l c.overG).obj B)) ≫
            (boundedConstructibleOpenImmersionLowerShriek _ l c.overI).map
              (K ◁ ε.hom.app B)) := by
  subst ε
  exact homMk_exceptionalProjectionMorphismOfCompactification_eq l c K B _
    (ι_map_eqToIso_trans_upperStarComp_inv_app_compactification (f := f) l c B)

end AlgebraicGeometry.ProEtale.CondensedRing
