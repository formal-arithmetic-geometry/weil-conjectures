/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCompositionCounitApex
public import Sheaf.AlgebraicGeometry.SchemeDerivedMateEvaluation
import Sheaf.AlgebraicGeometry.TensorPullbackCompositionHomotopyCounit

/-! # Counit calculations for pullback composition
Source: Stacks Project, Tags 079W, 0D5S and 0D5T.
(blueprint: lem-sc-derived-pullback-composition-counit-normalization).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory
namespace AlgebraicGeometry
attribute [local irreducible] Scheme.Modules.tensorPullback derivedPullback
private theorem combineCounit
    {C : Type*} [Category C] {A B T D : C}
    (p : A ⟶ B) (v : B ⟶ T) (d : T ⟶ D) (e : B ⟶ D)
    (q r : A ⟶ T) (z : A ⟶ D)
    (he : e = v ≫ d) (hq : p ≫ v = q) (hr : q = r) (hz : r ≫ d = z) :
    p ≫ e = z := by
  rw [he, ← Category.assoc, hq, hr, hz]

variable [∀ S : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]

set_option maxHeartbeats 800000 in
-- The selected adjunctions and composite sheaf instances need a larger budget.
/-- The chosen pullback comparison and composite direct-image unit transpose to the
explicit pasted underived counits.
Source: Stacks Project, Tags 079W, 0D5S and 0D5T.
(blueprint: lem-sc-derived-pullback-composition-counit-normalization).

Proof: Apply the pinned Hom formula at the underived counit for f ≫ g; its
adjunct is the identity by the right triangle identity. Thus L(fg) applied to β(fg),
followed by the derived counit, is ε(fg) at (fg)_*K followed by the localized
underived counit. Precompose with p. The defining left-derived lift factorization
replaces p followed by ε(fg) by Lf(ε(g)), ε(f), and the localized tensor
composition comparison. On a complex representative, the comparison is the inverse
mate of pushforwardComp, so its composite with the (fg)-counit is the pasted
g- and f-counits: apply conjugateEquiv_counit_symm degreewise, and use that
pushforwardComp is the identity on sections. Descend through the homotopy quotient
and apply localization. Naturality of ε(f) at the g-counit moves the localized
g-counit inside Lf and gives the displayed formula. Identities, zero complexes and
empty schemes use the same triangle and naturality equations. -/
theorem derivedPullbackComposition_counit_normalization
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (K : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (ComplexShape.up ℤ)) :
    (canonicalDerivedPullbackComposition f g).hom.app
        (((RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).obj K) ≫
      (derivedPullback (f ≫ g)).map
        ((RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom).rightDerivedFunctorUnit.app K) ≫
      (schemeHomPullbackAdjunction (f ≫ g)).counit.app (DerivedCategory.Qh.obj K) =
      derivedCompositionCounitApex f g K
    := by
  classical
  let ε {A B : Scheme.{u}} (s : A ⟶ B) :
      DerivedCategory.Qh ⋙ derivedPullback s ⟶
        (Scheme.Modules.tensorPullback s).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings A.toRingedSpace)) :=
    (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) s
  let a {A B : Scheme.{u}} (s : A ⟶ B) :
      Scheme.Modules.tensorPullback s ⊣ Scheme.Modules.pushforward s :=
    Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction s)
  let b {A B : Scheme.{u}} (s : A ⟶ B) :
      (Scheme.Modules.tensorPullback s).mapHomotopyCategory (ComplexShape.up ℤ) ⊣
        (Scheme.Modules.pushforward s).mapHomotopyCategory (ComplexShape.up ℤ) :=
    (a s).mapHomotopyCategory (ComplexShape.up ℤ)
  let U {A B : Scheme.{u}} (s : A ⟶ B) :
      HomotopyCategory (SheafOfModules.{u} (moduleRings A.toRingedSpace))
        (ComplexShape.up ℤ) ⥤
      HomotopyCategory (SheafOfModules.{u} (moduleRings B.toRingedSpace))
        (ComplexShape.up ℤ) :=
    (Scheme.Modules.pushforward s).mapHomotopyCategory (ComplexShape.up ℤ)
  have hn : (schemeHomPullbackAdjunction (f ≫ g)).homEquiv _ _
      ((ε (f ≫ g)).app ((U (f ≫ g)).obj K) ≫
        DerivedCategory.Qh.map ((b (f ≫ g)).counit.app K)) =
      (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings Z.toRingedSpace))).map
        ((b (f ≫ g)).homEquiv _ K ((b (f ≫ g)).counit.app K)) ≫
          (RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom).rightDerivedFunctorUnit.app
            K := by
    exact Classical.choose_spec (exists_schemeDerivedAdjunction (f ≫ g)
      (hAdd := (Classical.choose exists_derivedPullbackComposition) (f ≫ g))
      (ε (f ≫ g))
      ((Classical.choose (Classical.choose_spec
        (Classical.choose_spec exists_derivedPullbackComposition))) (f ≫ g)))
      ((U (f ≫ g)).obj K) K ((b (f ≫ g)).counit.app K)
  have hi : (b (f ≫ g)).homEquiv _ K ((b (f ≫ g)).counit.app K) = 𝟙 _ := by
    erw [← (b (f ≫ g)).homEquiv_symm_id, Equiv.apply_symm_apply]
  erw [hi, CategoryTheory.Functor.map_id, Category.id_comp] at hn
  have he : (derivedPullback (f ≫ g)).map
      ((RingedSpace.moduleDirectImage (f ≫ g).toLRSHom.toShHom).rightDerivedFunctorUnit.app K) ≫
        (schemeHomPullbackAdjunction (f ≫ g)).counit.app (DerivedCategory.Qh.obj K) =
      (ε (f ≫ g)).app ((U (f ≫ g)).obj K) ≫
        DerivedCategory.Qh.map ((b (f ≫ g)).counit.app K) :=
    (((schemeHomPullbackAdjunction (f ≫ g)).homEquiv _ _).eq_symm_apply.mpr hn).symm
  have : (derivedPullback (f ≫ g)).IsLeftDerivedFunctor (ε (f ≫ g))
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ)) :=
    (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) (f ≫ g)
  let c0 : Scheme.Modules.tensorPullback g ⋙ Scheme.Modules.tensorPullback f ≅
      Scheme.Modules.tensorPullback (f ≫ g) :=
    (conjugateIsoEquiv (a (f ≫ g)) ((a g).comp (a f))).symm
      (Scheme.Modules.pushforwardComp f g).symm
  let β : DerivedCategory.Qh ⋙ (derivedPullback g ⋙ derivedPullback f) ⟶
      (Scheme.Modules.tensorPullback (f ≫ g)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    ((Functor.associator DerivedCategory.Qh (derivedPullback g)
                (derivedPullback f)).inv ≫
              Functor.whiskerRight (ε g) (derivedPullback f) ≫
              (Functor.associator _ DerivedCategory.Qh (derivedPullback f)).hom ≫
              Functor.whiskerLeft _ (ε f) ≫
              (Functor.associator _ _
                (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace)))).inv ≫
              Functor.whiskerRight
                (Functor.mapHomotopyCategoryCompIso
                  c0 (ComplexShape.up ℤ)).hom
                (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))))
  have hc : (canonicalDerivedPullbackComposition f g).hom =
      (derivedPullback (f ≫ g)).leftDerivedLift (ε (f ≫ g))
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ))
        (derivedPullback g ⋙ derivedPullback f) β :=
    (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))).1 f g
  let M := (U (f ≫ g)).obj K
  let d :=
    (DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).map
      ((b (f ≫ g)).counit.app K)
  have hfac := (derivedPullback (f ≫ g)).leftDerived_fac_app
    (ε (f ≫ g))
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (ComplexShape.up ℤ))
    (derivedPullback g ⋙ derivedPullback f) β M
  have hp := congrArg (fun t => t.app (DerivedCategory.Qh.obj M) ≫
    (ε (f ≫ g)).app M) hc
  have hfactor := hp.trans hfac
  have hβ : β.app M =
      (derivedPullback f).map ((ε g).app M) ≫
        (ε f).app
          (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
        (DerivedCategory.Qh (C :=
          SheafOfModules.{u} (moduleRings X.toRingedSpace))).map
          ((Functor.mapHomotopyCategoryCompIso c0 (ComplexShape.up ℤ)).hom.app M) := by
    dsimp only [β, NatTrans.comp_app, Functor.associator,
      Functor.whiskerRight, Functor.whiskerLeft]
    simp only [Category.id_comp]
  have hN := tensorPullbackComposition_localized_homotopy_counit f g
    K
  dsimp only at hN
  exact combineCounit
    ((canonicalDerivedPullbackComposition f g).hom.app (DerivedCategory.Qh.obj M))
    ((ε (f ≫ g)).app M) d _ (β.app M) _ (derivedCompositionCounitApex f g K)
    he hfactor hβ (by simpa only [ε, a, b, c0, U, M, d] using hN)

end AlgebraicGeometry
