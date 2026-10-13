/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q4
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! # The affine derived edge before choosing module coordinates

Source: Stacks Project, Tags 0AVW and 08D4.
(blueprint: lem-pc-affine-derived-pushforward-sheaf-edge). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The sheaf-level affine edge is compatible with the actual derived unit on an
exact family of quasi-coherent sheaves. No tilde/Gamma coordinates or ordinary
comparison isomorphism occur here.
Source: Stacks Project, Tag 0AVW, proof of lemma-affine-morphism-equivalence,
and Tag 08D4, lemma-application-nice-K-injective with bound one.
(blueprint: lem-pc-affine-derived-pushforward-sheaf-edge).

Proof: On the inverse image of an affine open, higher cohomology of a
quasi-coherent module vanishes. Apply the bound-one truncation calculation of
08D4 to a K-injective resolution, in degree i. Its cycle-class comparison
identifies cohomology of derived sections with sections of the cohomology
sheaf. These comparisons commute with restrictions and derived morphisms;
sheafifying them gives the edge f_*H^i -> H^i Rf_* on D_QCoh. For an exact
functor F with quasi-coherent values, compare the complex F(C) with its
K-injective resolution. The comparison from termwise pushforward is the
right-derived unit. Exactness of F and f_*F identifies its source cohomology
with F(H^i C) and f_*F(H^i C), respectively. On cycles both resulting arrows
send the same section to its class in the resolution; the cokernel universal
property proves the displayed equality. Restriction-compatible equality on
the affine basis proves equality of sheaf morphisms. This applies to unbounded
C by 08D4; neither the zero ring nor zero complexes need to be excluded. -/
theorem exists_affineDerivedPushforwardSheafEdge
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ) :
  ∃ ε : (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i ⋙
      RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom ⟶
    (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ)) ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i,
    ∀ (F : ModuleCat.{u} A ⥤
        SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
      [F.Additive] [F.PreservesZeroMorphisms] [F.PreservesHomology]
      [(F ⋙ RingedSpace.moduleDirectImage
        (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).PreservesZeroMorphisms]
      [(F ⋙ RingedSpace.moduleDirectImage
        (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).PreservesHomology]
      (_hF : ∀ M, (F.obj M).IsQuasicoherent)
      (C : CochainComplex (ModuleCat.{u} A) ℤ)
      (hC : schemeDerivedQCohProperty (Spec (.of A))
        (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj C))),
      (RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).map
          (((C.sc i).mapHomologyIso F).inv ≫
            ((DerivedCategory.homologyFunctorFactors _ i).app
              ((F.mapHomologicalComplex (.up ℤ)).obj C)).inv) ≫
        ε.app ⟨_, hC⟩ =
      ((C.sc i).mapHomologyIso
        (F ⋙ RingedSpace.moduleDirectImage
          (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom)).inv ≫
        ((DerivedCategory.homologyFunctorFactors _ i).app
          (((F ⋙ RingedSpace.moduleDirectImage
            (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom)
              |>.mapHomologicalComplex (.up ℤ)).obj C)).inv ≫
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).map
          (((RingedSpace.moduleDirectImage
            (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).rightDerivedFunctorUnit).app
            ((HomotopyCategory.quotient _ (.up ℤ)).obj
              ((F.mapHomologicalComplex (.up ℤ)).obj C))) := by sorry

end AlgebraicGeometry
