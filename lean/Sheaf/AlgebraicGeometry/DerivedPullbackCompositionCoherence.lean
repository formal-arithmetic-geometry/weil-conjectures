/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import Sheaf.Algebra.Homology.KFlatPullback
import Sheaf.Algebra.Homology.KFlatResolution

/-! Canonical derived pullback comparison: Stacks Project, Tag 0D5S. -/

@[expose] public section

universe u₁ w₁
open CategoryTheory
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry

/-- Canonical composition comparisons have identity comparisons and satisfy coherence.
Source: Stacks Project, Cohomology, Tag 0D5S, with the tensor unit and associativity laws.
(blueprint: lem-pc-derived-pullback-comparison-coherence).
Proof: the identity tensor pullback is isomorphic to the identity functor by the
conjugate of the pushforward identity comparison under the pinned adjunction.
On a K-flat complex the identity counit is invertible, so this comparison descends
to an isomorphism L(id)* ≅ id by the universal property and K-flat resolutions.
For each unit law, whisker the proposed equality with Qh and compose with the
counit. The defining factorization hc and tensor unit law give equal maps on
K-flat complexes. Resolve every complex to descend the equality; uniqueness of
maps into the left-derived functor gives equality of natural transformations.
For associativity the same factorization rewrites both paths on a K-flat complex
as three successive counits followed by the underived tensor comparison. The
conjugates of pushforwardComp are associative by the adjunction mate calculus
and pushforward associativity. Concretely, use
Adjunction.leftAdjointCompIso_comp_id, Adjunction.leftAdjointCompIso_id_comp,
and Adjunction.leftAdjointCompIso_assoc for the underived comparisons.
Resolve complexes and use naturality and essential surjectivity of Qh
to extend component equalities to all derived objects. Equality of homs implies
equality of the resulting isomorphisms.
Empty schemes and identity morphisms require no extra hypotheses. -/
theorem derivedPullbackComposition_coherence
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
                (DerivedCategory.Qh (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))).inv ≫
              Functor.whiskerRight
                (Functor.mapHomotopyCategoryCompIso
                  ((conjugateIsoEquiv
                    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (f ≫ g)))
                    ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).comp
                      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)))).symm
                    (Scheme.Modules.pushforwardComp f g).symm)
                  (ComplexShape.up ℤ)).hom
                (DerivedCategory.Qh (C := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)))))
    : ∃ i : ∀ X : Scheme.{u₁}, derivedPullback (𝟙 X) ≅ 𝟭 _,
        (∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y),
          c (𝟙 X) f ≪≫
            eqToIso (congrArg (fun k : X ⟶ Y => derivedPullback k) (Category.id_comp f)) =
            Functor.isoWhiskerLeft (derivedPullback f) (i X) ≪≫
              Functor.rightUnitor (derivedPullback f)) ∧
        (∀ {X Y : Scheme.{u₁}} (f : X ⟶ Y),
          c f (𝟙 Y) ≪≫
            eqToIso (congrArg (fun k : X ⟶ Y => derivedPullback k) (Category.comp_id f)) =
            Functor.isoWhiskerRight (i Y) (derivedPullback f) ≪≫
              Functor.leftUnitor (derivedPullback f)) ∧
        (∀ {W X Y Z : Scheme.{u₁}} (h : W ⟶ X) (f : X ⟶ Y) (g : Y ⟶ Z),
          Functor.isoWhiskerRight (c f g) (derivedPullback h) ≪≫ c h (f ≫ g) =
            Functor.associator (derivedPullback g) (derivedPullback f)
                (derivedPullback h) ≪≫
              Functor.isoWhiskerLeft (derivedPullback g) (c h f) ≪≫ c (h ≫ f) g ≪≫
                eqToIso (congrArg (fun k : W ⟶ Z => derivedPullback k)
                  (Category.assoc h f g))) := by
  sorry

end AlgebraicGeometry
