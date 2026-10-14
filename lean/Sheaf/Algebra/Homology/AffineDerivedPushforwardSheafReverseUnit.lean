/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G4
-/
module
public import Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdgeCanonical

/-! # The reverse cycle-class comparison and the derived unit -/

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

/-- On an arbitrary representative with quasi-coherent cohomology, homology of the
right-derived unit followed by the fixed reverse comparison is the explicit kernel
lift/cokernel descent comparison. There is no module-valued exact family in this statement.
Source: Stacks Project, Tags 0AVW and 08D4, comparison with a K-injective resolution.
(blueprint: lem-pc-affine-derived-pushforward-sheaf-reverse-unit).

Proof: Choose a quasi-isomorphism q:D→I with I K-injective. Preservation of kernels
makes the cycles lift natural in q; precomposition with the homology projection proves
naturality of the reverse homology map by the cokernel universal property. Apply this
square to q and transport through the localization/homology factors. Naturality of the
right-derived unit replaces its component at D by its component at I followed by the
mapped q. At I the asserted formula is the defining K-injective characterization of
the unique reverse comparison; the unit there is invertible. Naturality of that
comparison with Q(q), and cancellation of homology of Q(q), give the desired formula.
Only Q(q) needs to be invertible: termwise pushforward of q need not be a quasi-isomorphism.
This works for zero objects and arbitrary unbounded representatives. -/
theorem affineDerivedPushforwardSheafReverse_unit
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ)
    (D : CochainComplex
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) ℤ)
    (hD : schemeDerivedQCohProperty (Spec (.of A)) (DerivedCategory.Q.obj D)) :
    (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i).map
        (((RingedSpace.moduleDirectImage
          (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).rightDerivedFunctorUnit).app
          ((HomotopyCategory.quotient _ (.up ℤ)).obj D)) ≫
        (affineDerivedPushforwardSheafReverseIso A B φ i).hom.app ⟨_, hD⟩ =
      ((DerivedCategory.homologyFunctorFactors _ i).app
        (((RingedSpace.moduleDirectImage
          (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).mapHomologicalComplex
            (.up ℤ)).obj D)).hom ≫
      (D.sc i).leftExactHomologyComparison
        (RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom) ≫
      (RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom).map
        (((DerivedCategory.homologyFunctorFactors _ i).app D).inv) := by
  sorry
end AlgebraicGeometry
