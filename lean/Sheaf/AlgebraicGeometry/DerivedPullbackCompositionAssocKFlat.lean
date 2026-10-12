/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import Sheaf.Algebra.Homology.KFlatPullback

/-! Associativity calculation on K-flat representatives for derived pullback. -/

@[expose] public section

universe u₁ w₁
open CategoryTheory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry

/-- The two triple-composition paths have equal components on a K-flat complex.
Source: Stacks Project, Cohomology, Tag 0D5S, Lemma 20.27.2;
Mathlib `Adjunction.leftAdjointCompIso_assoc`.
(blueprint: lem-pc-derived-pullback-assoc-kflat).
Proof: let H be the homotopy image of P. Tensor pullback by g, and then by f,
preserves K-flatness (lem-pc-kflat-pullback-preservation). Thus hK makes the
successive counits invertible, both at H and at its tensor pullbacks. Evaluate
hc for (f,g), (h,f), (h,f≫g), and (h≫f,g) and use leftDerived_fac_app.
Postcompose each of the proposed paths with the counit of h≫f≫g at H.
Naturality moves each counit past the preceding comparison; associators of
functors have identity components. After these rewrites each side is the
same ordered sequence: the counit of g at H, the counit of f at its tensor
pullback, the counit of h at the second tensor pullback, and then the
underived triple tensor comparison mapped by Qh. The two underived comparisons
are equal by leftAdjointCompIso_assoc applied to the pinned adjunctions and
the pushforward associativity law. Transport along Category.assoc carries
the adjunction for the composite to the same pinned adjunction; thus the
mate calculation includes precisely the eqToIso in the displayed formula.
Cancel the invertible final counit hK (h≫f≫g) P hP. This gives the component
equality, without resolving any other complex or asserting global coherence.
The calculation works for zero complexes, empty schemes, and identity morphisms. -/
theorem derivedPullbackComposition_assoc_kflat
    [d : ∀ X : Scheme.{u₁}, HasDerivedCategory.{w₁}
      (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    (a : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y), (Scheme.Modules.tensorPullback f).Additive)
      (ε : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y),
        DerivedCategory.Qh ⋙ derivedPullback f ⟶
          (Scheme.Modules.tensorPullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
            DerivedCategory.Qh (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))
      (hL : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y),
        (derivedPullback f).IsLeftDerivedFunctor (ε f)
          (HomotopyCategory.quasiIso
            (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace)) (ComplexShape.up ℤ)))
    (hK : ∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y)
      (P : CochainComplex (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace)) ℤ),
      CochainComplex.IsKFlat (R := Y.sheaf) P →
        IsIso ((ε f).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)))
    (c : ∀ {X Y Z : Scheme.{u₁}} (f : X ⟶ Y) (g : Y ⟶ Z),
        derivedPullback g ⋙ derivedPullback f ≅ derivedPullback (f ≫ g))
    (hc :∀ {X Y Z : Scheme.{u₁}} (f : X ⟶ Y) (g : Y ⟶ Z),
        (c f g).hom =
          (derivedPullback (f ≫ g)).leftDerivedLift (ε (f ≫ g))
            (HomotopyCategory.quasiIso
              (SheafOfModules.{u₁} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ))
            (derivedPullback g ⋙ derivedPullback f)
            ((Functor.associator DerivedCategory.Qh (derivedPullback g)
                (derivedPullback f)).inv ≫
              Functor.whiskerRight (ε g) (derivedPullback f) ≫
              (Functor.associator _ DerivedCategory.Qh (derivedPullback f)).hom ≫
              Functor.whiskerLeft _ (ε f) ≫
              (Functor.associator _ _
                (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))).inv ≫
              Functor.whiskerRight
                (Functor.mapHomotopyCategoryCompIso
                  ((conjugateIsoEquiv
                    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
                    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
                      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
                    (Scheme.Modules.pushforwardComp f g).symm)
                  (ComplexShape.up ℤ)).hom
                (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))))
    {W X Y Z : Scheme.{u₁}} (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : CochainComplex (SheafOfModules.{u₁} (moduleRings Z.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlat (R := Z.sheaf) P) :
    (Functor.isoWhiskerRight (c f g) (derivedPullback h) ≪≫ c h (f ≫ g)).hom.app
      (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) =
    (Functor.associator (derivedPullback g) (derivedPullback f)
        (derivedPullback h) ≪≫
      Functor.isoWhiskerLeft (derivedPullback g) (c h f) ≪≫ c (h ≫ f) g ≪≫
        eqToIso (congrArg (fun k : W ⟶ Z ↦ derivedPullback k)
          (Category.assoc h f g))).hom.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) := by sorry

end AlgebraicGeometry
