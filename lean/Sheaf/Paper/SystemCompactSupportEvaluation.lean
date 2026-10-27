module

public import Sheaf.Paper.SystemCompactSupportData
public import Sheaf.AlgebraicGeometry.EtaleSupportProjectionShiftUnit

/-! # Evaluation of the canonical system projection word

Source: Zheng Lemma 5.16; Stacks 0B56 and 0GL1
(blueprint: def-coef-system-compact-support-evaluation).
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
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemCompactSupport
open SystemProjection

/-- The fixed coefficient tensor bifunctor, in coefficient-first order.
Source: Stacks 0B56 (blueprint: def-coef-system-compact-support-evaluation). -/
abbrev fixedTensor (W : Scheme.{u}) (A : CommRingCat.{u + 1}) :=
  Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} A) W)

/-- Exact pullback followed by the canonical comparison with total left derivation.
Source: Stacks 07A4 (blueprint: def-coef-system-compact-support-evaluation). -/
def finitePullComposition {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (A : CommRingCat.{u + 1}) :
    (upperStar (ModuleCat.{u + 1} A) c.g).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) c.i).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor :=
  Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) c.g).symm _ ≪≫
    Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) c.i).symm ≪≫
    leftDerivedUpperStarCompactificationIso (ModuleCat.{u + 1} A) c

/-- Evaluation of aX-star as the composite aY-star, p-star, j-star, including the
published comparison to the finite projection's exact derived pullback.
Source: Zheng Lemma 5.16 (blueprint: def-coef-system-compact-support-evaluation). -/
def ProjectionEvaluation.pullComparison {S X Y : Scheme.{u}} {f : X ⟶ Y}
    {c : Compactification f} {aY : Y ⟶ S} {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}}
    {d : ProjectionData c aY B} (e : ProjectionEvaluation d) (n : ℕ) (P : Derived S B) :
    (e.ex n).E.obj (d.pull.obj P) ⟶
      (upperStar (ModuleCat.{u + 1} (B.obj (op n))) f).leftDerivedFunctor.obj
        ((upperStar (ModuleCat.{u + 1} (B.obj (op n))) aY).mapDerivedCategory.obj
          ((e.es n).E.obj P)) :=
  (e.openImage n).derivedInverse.inv.app
      (d.support.proper.P.obj (d.baseImage.P.obj P)) ≫
    (upperStar (ModuleCat.{u + 1} (B.obj (op n))) c.i).mapDerivedCategory.map
      ((e.support n).proper.derivedInverse.inv.app (d.baseImage.P.obj P)) ≫
    (upperStar (ModuleCat.{u + 1} (B.obj (op n))) c.i).mapDerivedCategory.map
      ((upperStar (ModuleCat.{u + 1} (B.obj (op n))) c.g).mapDerivedCategory.map
        ((e.base n).derivedInverse.inv.app P)) ≫
    (finitePullComposition c (B.obj (op n))).hom.app
      ((upperStar (ModuleCat.{u + 1} (B.obj (op n))) aY).mapDerivedCategory.obj
        ((e.es n).E.obj P))

/-- The finite projection comparison equation, retaining its canonical conjugations.
This compares maps, rather than merely asserting that their sources are isomorphic.
Source: Stacks 0B56, 0GL1 (blueprint: def-coef-system-compact-support-evaluation). -/
def ProjectionEvaluation.projectionLaw {S X Y : Scheme.{u}} {f : X ⟶ Y}
    {c : Compactification f} {aY : Y ⟶ S} {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}}
    {d : ProjectionData c aY B} (e : ProjectionEvaluation d)
    (pi : d.source ⟶ d.target) : Prop :=
  ∀ (n : ℕ) (P : Derived S B) (M : Derived X B),
    (e.ey n).E.map (pi.app (P, M)) ≫
        (e.support n).iso.hom.app (d.x.closed.tensor.obj (d.pull.obj P, M)) ≫
        (rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (B.obj (op n))) c).map
          ((e.tx n).tensor.hom.app (d.pull.obj P, M) ≫
            (fixedTensor X (B.obj (op n))).map
              (Prod.mkHom (e.pullComparison n P) (𝟙 _))) =
      (e.ty n).tensor.hom.app (d.baseImage.P.obj P, d.support.F.obj M) ≫
        (fixedTensor Y (B.obj (op n))).map
          (Prod.mkHom ((e.base n).derivedInverse.inv.app P)
            ((e.support n).iso.hom.app M)) ≫
        ((supportProjectionMap (ModuleCat.{u + 1} (B.obj (op n))) c).app
          ((e.ex n).E.obj M)).app
            ((upperStar (ModuleCat.{u + 1} (B.obj (op n))) aY).mapDerivedCategory.obj
              ((e.es n).E.obj P))

end AlgebraicGeometry.Etale.SystemCompactSupport
