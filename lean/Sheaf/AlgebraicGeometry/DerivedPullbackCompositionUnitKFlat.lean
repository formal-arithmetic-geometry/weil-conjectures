/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory

/-! Unit calculations on K-flat representatives for derived pullback. -/

@[expose] public section

universe u₁ w₁
open CategoryTheory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry

/-- The two unit comparisons agree on a K-flat representative, for identity
isomorphisms normalized by the tensor identity mate.
Source: Stacks Project, Cohomology, Tag 0D5S, Lemma 20.27.2;
Mathlib `Adjunction.leftAdjointCompIso_comp_id` and
`Adjunction.leftAdjointCompIso_id_comp`.
(blueprint: lem-pc-derived-pullback-unit-kflat).
Proof: write H for the homotopy image of P. Apply hc to the hom of each
composition comparison and use leftDerived_fac_app at H. The resulting expression
is the two successive counits followed by the homotopy image of the tensor
composition mate. For c(id_X,f), naturality of the counit of id_X moves the
counit of f past it. Substitute hi X evaluated at the tensor pullback of H;
this replaces the identity counit followed by the tensor identity mate by
Qh applied to i X. For c(f,id_Y), substitute hi Y at H and use naturality
of the counit of f. The underived identities are respectively
leftAdjointCompIso_comp_id and leftAdjointCompIso_id_comp, applied to the
pinned adjunctions and pushforward identity laws. When rewriting id_comp or
comp_id, transport the pinned adjunctions as well; conjugateIsoEquiv is natural
under that transport. The homotopy images and Qh preserve these equalities.
The two expressions now agree after postcomposition with the counit of f
at H. This counit is invertible by hK f P hP, so cancel it. Functor unitors
have identity components, giving the two displayed component equalities.
No nonempty, flat-morphism, or boundedness hypothesis is used: the argument also
applies to zero complexes, empty schemes, and f an identity. -/
theorem derivedPullbackComposition_unit_kflat
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
    (i : ∀ X : Scheme.{u₁}, derivedPullback (𝟙 X) ≅ 𝟭 _)
    (hi : ∀ X : Scheme.{u₁},
        Functor.whiskerLeft (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace))) (i X).hom ≫
            (Functor.rightUnitor (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))).hom =
          ε (𝟙 X) ≫
            Functor.whiskerRight
              (NatTrans.mapHomotopyCategory
                (Adjunction.leftAdjointIdIso
                  (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (𝟙 X)))
                  (Scheme.Modules.pushforwardId X)).hom (ComplexShape.up ℤ))
              (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace))) ≫
            Functor.whiskerRight
              (Functor.mapHomotopyCategoryIdIso
                (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))
                (ComplexShape.up ℤ)).hom (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace))) ≫
            (Functor.leftUnitor (DerivedCategory.Qh
          (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))).hom)
    {X Y : Scheme.{u₁}} (f : X ⟶ Y)
    (P : CochainComplex (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlat (R := Y.sheaf) P) :
    ((c (𝟙 X) f ≪≫
        eqToIso (congrArg (fun k : X ⟶ Y ↦ derivedPullback k) (Category.id_comp f))).hom.app
      (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) =
    (Functor.isoWhiskerLeft (derivedPullback f) (i X) ≪≫
      Functor.rightUnitor (derivedPullback f)).hom.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) ∧
    ((c f (𝟙 Y) ≪≫
        eqToIso (congrArg (fun k : X ⟶ Y ↦ derivedPullback k) (Category.comp_id f))).hom.app
      (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P)) =
    (Functor.isoWhiskerRight (i Y) (derivedPullback f) ≪≫
      Functor.leftUnitor (derivedPullback f)).hom.app (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj P))) := by sorry

end AlgebraicGeometry
