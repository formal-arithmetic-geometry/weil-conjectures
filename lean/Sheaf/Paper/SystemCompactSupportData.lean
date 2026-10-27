module

public import Sheaf.Paper.EtaleSystemImageTensor

/-! # Canonical compact-support projection data on strict systems

Source: Zheng Constructions 5.14--5.15; Stacks 0B56, 0GL1, 0GL6
(blueprint: def-coef-system-compact-support-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures.SemilinearSections
namespace AlgebraicGeometry.Etale.SystemCompactSupport
open SystemProjection

/-- The actual tensor and geometric operations, not assumptions on their existence.
The open comparison is fixed by its adjunction transpose before evaluating systems.
Source: Stacks 0B56 and 0GL1
(blueprint: def-coef-system-compact-support-data). -/
structure ProjectionData {S X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (aY : Y ⟶ S) (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) where
  support : Support c B
  base : Calculus S B
  x : Calculus X B
  y : Calculus Y B
  z : Calculus c.Z B
  baseImage : Image aY B
  properTensor : ImageTensor support.proper y z
  openTensor : ImageTensor support.openImage.toImage z x
  openProjection :
    ((support.openImage.toImage.P.prod (𝟭 (Derived X B))) ⋙ x.closed.tensor) ⋙
        support.openImage.J ≅
      ((𝟭 (Derived c.Z B)).prod support.openImage.J) ⋙ z.closed.tensor
  openProjection_transpose : ∀ (H : Derived c.Z B) (M : Derived X B),
    (support.openImage.derivedAdjunction.homEquiv _ _)
        (openProjection.hom.app (H, M)) =
      x.closed.tensor.map
          (Prod.mkHom (𝟙 (support.openImage.toImage.P.obj H))
            (support.openImage.derivedAdjunction.unit.app M)) ≫
        openTensor.mu.inv.app (H, support.openImage.J.obj M)

/-- The pullback from the base along aY, p, and j. Its composite is aX by f = jp.
Source: Zheng Construction 5.15 (blueprint: def-coef-system-compact-support-data). -/
abbrev ProjectionData.pull {S X Y : Scheme.{u}} {f : X ⟶ Y}
    {c : Compactification f} {aY : Y ⟶ S} {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}}
    (d : ProjectionData c aY B) :=
  d.baseImage.P ⋙ d.support.proper.P ⋙ d.support.openImage.toImage.P

/-- The proper projection is exactly the transpose of tensor pullback and counit.
Source: Stacks 0B56 (blueprint: def-coef-system-compact-support-data). -/
def ProjectionData.properWord {S X Y : Scheme.{u}} {f : X ⟶ Y}
    {c : Compactification f} {aY : Y ⟶ S} {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}}
    (d : ProjectionData c aY B) (H : Derived Y B) (N : Derived c.Z B) :
    d.y.closed.tensor.obj (H, d.support.proper.R.obj N) ⟶
      d.support.proper.R.obj (d.z.closed.tensor.obj (d.support.proper.P.obj H, N)) :=
  d.support.proper.derivedAdjunction.homEquiv _ _
    (d.properTensor.mu.hom.app (H, d.support.proper.R.obj N) ≫
      d.z.closed.tensor.map
        (Prod.mkHom (𝟙 _) (d.support.proper.derivedAdjunction.counit.app N)))

/-- The whole-system compact-support projection word, constructed before evaluation.
Source: Stacks 0B56 and 0GL1 (blueprint: def-coef-system-compact-support-data). -/
def ProjectionData.word {S X Y : Scheme.{u}} {f : X ⟶ Y}
    {c : Compactification f} {aY : Y ⟶ S} {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}}
    (d : ProjectionData c aY B) (P : Derived S B) (M : Derived X B) :
    d.y.closed.tensor.obj (d.baseImage.P.obj P, d.support.F.obj M) ⟶
      d.support.F.obj (d.x.closed.tensor.obj (d.pull.obj P, M)) :=
  d.properWord (d.baseImage.P.obj P) (d.support.openImage.J.obj M) ≫
    d.support.proper.R.map
      (d.openProjection.inv.app (d.support.proper.P.obj (d.baseImage.P.obj P), M))

/-- Source of the projection as a bifunctor on the actual unbounded categories.
Source: Stacks 0B56 (blueprint: def-coef-system-compact-support-data). -/
def ProjectionData.source {S X Y : Scheme.{u}} {f : X ⟶ Y}
    {c : Compactification f} {aY : Y ⟶ S} {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}}
    (d : ProjectionData c aY B) :=
  (d.baseImage.P.prod d.support.F) ⋙ d.y.closed.tensor

/-- Target of the projection with the geometric pullback from the base.
Source: Stacks 0B56 (blueprint: def-coef-system-compact-support-data). -/
def ProjectionData.target {S X Y : Scheme.{u}} {f : X ⟶ Y}
    {c : Compactification f} {aY : Y ⟶ S} {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}}
    (d : ProjectionData c aY B) :=
  ((d.pull.prod (𝟭 (Derived X B))) ⋙ d.x.closed.tensor) ⋙ d.support.F

/-- All evaluation identifications come from the actual ordinary adjunctions.
The tensor evaluations retain their pure-tensor and K-flat normalizations.
Source: Zheng Lemma 5.16; Stacks 0GL6
(blueprint: def-coef-system-compact-support-data). -/
structure ProjectionEvaluation {S X Y : Scheme.{u}} {f : X ⟶ Y}
    {c : Compactification f} {aY : Y ⟶ S} {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}}
    (d : ProjectionData c aY B) where
  es : ∀ n : ℕ, Evaluation S B n
  ex : ∀ n : ℕ, Evaluation X B n
  ey : ∀ n : ℕ, Evaluation Y B n
  ez : ∀ n : ℕ, Evaluation c.Z B n
  tx : ∀ n : ℕ, TensorEvaluation X B d.x n (ex n)
  ty : ∀ n : ℕ, TensorEvaluation Y B d.y n (ey n)
  support : ∀ n : ℕ, SupportEvaluation d.support n (ex n) (ez n) (ey n)
  base : ∀ n : ℕ, ImageEvaluation d.baseImage n (ey n) (es n)
    (upperStar (ModuleCat.{u + 1} (B.obj (op n))) aY)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (B.obj (op n))) aY)
  openImage : ∀ n : ℕ, ImageEvaluation d.support.openImage.toImage n (ex n) (ez n)
    (upperStar (ModuleCat.{u + 1} (B.obj (op n))) c.i)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (B.obj (op n))) c.i)

end AlgebraicGeometry.Etale.SystemCompactSupport
