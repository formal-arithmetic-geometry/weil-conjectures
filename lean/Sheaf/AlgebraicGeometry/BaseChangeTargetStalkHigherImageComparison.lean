/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeStalkTransition

/-! # Comparison of target stalks with fixed-coefficient higher images

Source: Stacks Project Tags 0F07 and 09Z1.
(blueprint: lem-sbc-target-stalk-higher-image-comparison)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The target stalk system is the higher-image stalk system of the fixed sheaf
pulled back to `T ×_S X`, naturally in schemes over `T`.

Source: Stacks Project Tag 0F07, the restriction square and coefficient
identification preceding condition (2), and Tag 09Z1, canonical restriction maps.
(blueprint: lem-sbc-target-stalk-higher-image-comparison)

Proof: Put W = T ×_S X and G = pr_T^* F. For U over T, the iterated pullback
U ×_T W is canonically isomorphic to U ×_S X, preserving its projections to U
and X. Transport higher direct image along this scheme isomorphism. Composition
of inverse images identifies the pullback of G to U ×_T W with the pullback of
U.hom^* F to U ×_S X. The single-complex comparison for the exact inverse-image
functor, followed by degree-q homology, identifies this higher image with the
base-change target functor. Apply the geometric stalk functor to these
isomorphisms. For a morphism U → V over T, expand both restriction maps as the
unit, inverse-image composition comparison, and counit of the derived
adjunction. Naturality of unit and counit and associativity of inverse-image
composition give the displayed commuting square. This works in every integer
degree, including negative degrees, since all comparisons are derived
isomorphisms before taking homology.
-/
theorem baseChange_target_stalk_higher_image_comparison
    (Λ : Type (u + 1)) [CommRing Λ] {X S T : Scheme.{u}}
    (p : X ⟶ S) (g : T ⟶ S) (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (x : X) :
    let B := Over.pullback (pullback.fst g p)
    let G := ((pullback.fst g p)^*[ModuleCat.{u + 1} Λ]).obj F
    ∃ E : ∀ U : Over T, baseChangeTargetStalk Λ p g q F x U ≅
        (X.uliftPointSmallEtale x).sheafFiber.obj
          (higherDirectImage Λ ((B.obj U).hom ≫ pullback.snd g p) q
            ((((B.obj U).hom)^*[ModuleCat.{u + 1} Λ]).obj G)),
      ∀ (U V : Over T) (φ : U ⟶ V),
        baseChangeTargetStalkMap Λ p g q F x φ ≫ (E U).hom =
          (E V).hom ≫ (X.uliftPointSmallEtale x).sheafFiber.map
            (higherDirectImageOverMap Λ (pullback.snd g p) G q (B.map φ)) := by sorry

end AlgebraicGeometry.Etale
