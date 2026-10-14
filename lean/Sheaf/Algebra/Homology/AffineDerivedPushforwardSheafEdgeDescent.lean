/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.Algebra.Homology.LeftExactHomologyComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-! # Descent of the affine reverse comparison from K-injectives

The comparison is specified on K-injective representatives by an explicit kernel/cokernel
construction, independently of any compatibility for exact module-valued families. -/

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

/-- Direct image preserves finite limits: it is the sheaf module pushforward,
a right adjoint. Source: Stacks Project, Tag 079V. -/
instance affineEdge_moduleDirectImage_preservesFiniteLimits {X Y : RingedSpace.{u}}
    (g : X ⟶ Y) : PreservesFiniteLimits (RingedSpace.moduleDirectImage g) := by
  dsimp [RingedSpace.moduleDirectImage]
  infer_instance

/-- Reverse comparison on a K-injective complex: compute derived direct image by
its unit, compare cohomology of termwise pushforward to pushforward of cohomology,
and transport back through the localization/homology comparison.
Source: Stacks Project, Tag 0AVW, cohomology display in the proof. -/
def affineKInjectiveReverseComparison
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ)
    (I : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    [I.IsKInjective] :
    (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).obj
      ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ))).obj
        (DerivedCategory.Q.obj I)) ⟶
    (RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).obj
      ((DerivedCategory.homologyFunctor _ i).obj (DerivedCategory.Q.obj I)) := by
  let P := RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i
  exact H.map (P.rightDerivedFunctorObjQIso I).hom ≫
    ((DerivedCategory.homologyFunctorFactors _ i).app
      ((P.mapHomologicalComplex (.up ℤ)).obj I)).hom ≫
    (I.sc i).leftExactHomologyComparison P ≫
    P.map (((DerivedCategory.homologyFunctorFactors _ i).app I).inv)

/-- The explicit reverse comparisons on K-injectives descend to a unique natural
isomorphism on the quasi-coherent derived category.
Source: Stacks Project, Tags 0AVW (affine cohomology display), 08D4 (bound one),
and localization by K-injective resolutions.
(blueprint: lem-pc-affine-derived-pushforward-sheaf-edge-descent).

Proof: Pushforward preserves kernels, so the displayed kernel lift followed by the
mapped cycle-class projection annihilates boundaries. It therefore descends through
homology. Kernel and cokernel universal properties prove naturality for chain maps;
homotopic maps have the same homology map, so it is natural on the K-injective homotopy
category. On every affine open of Spec B, its inverse image is affine, and sections
have cohomological bound one on quasi-coherent sheaves. Tag 08D4 removes both tails;
the resulting degree-i cycle-class comparison is exactly the displayed reverse map.
Affine vanishing makes it invertible on that basis, hence on sheaves. K-injectives
with quasi-coherent cohomology localize equivalently to D_QCoh: transport the natural
comparison along this equivalence and the right-derived-unit isomorphism to obtain
τ. Every object admits such a representative, so naturality with the representative
isomorphism determines every component of τ. Thus τ is unique, including its inverse.
No exact functor F or compatibility equation from the component theorem is used. -/
theorem existsUnique_affineDerivedPushforwardReverseComparison
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ) :
    ∃! τ : (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
        schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ)) ⋙
        DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i ≅
      (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
        DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i ⋙
        RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom,
      ∀ (I : CochainComplex
          (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
        [I.IsKInjective]
        (hI : schemeDerivedQCohProperty (Spec (.of A)) (DerivedCategory.Q.obj I)),
        τ.hom.app ⟨_, hI⟩ = affineKInjectiveReverseComparison A B φ i I := by
  sorry
end AlgebraicGeometry
