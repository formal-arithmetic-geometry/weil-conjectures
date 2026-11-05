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
  NatIso.ofComponents (fun N ↦ ObjectProperty.isoMk _
    ((leftDerivedUpperStarOverCompactificationIso (f := f) Λ c).symm.app N.obj))
    (fun φ ↦ ObjectProperty.hom_ext _
      ((leftDerivedUpperStarOverCompactificationIso (f := f) Λ c).inv.naturality φ.hom))

/-- The underlying component is the inverse of the ambient composition comparison. -/
lemma compactProjectionGeometricPullIso_hom_app (N : Dᵇc(Y.left)⟦Λ⟧) :
    ((compactProjectionGeometricPullIso Λ l c).hom.app N).hom =
      (leftDerivedUpperStarOverCompactificationIso (f := f) Λ c).inv.app N.obj := rfl

/-- The geometric exceptional projection factors through the canonical pullback compositor. -/
lemma compactProjectionGeometricPullIso_projection_eq
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
              (K ◁ (compactProjectionGeometricPullIso _ l c).hom.app B)) :=
  homMk_exceptionalProjectionMorphismOfCompactification_eq l c K B _
    (compactProjectionGeometricPullIso_hom_app _ l c B)

end AlgebraicGeometry.ProEtale.CondensedRing
