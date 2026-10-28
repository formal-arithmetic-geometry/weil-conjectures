/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.Paper.RationalP1SecondPretraceData

/-! # Scalar evaluation of the normalized projective-line projection mate

Source: the First identity in the current rational projective-line triangle proof.
(blueprint: lem-sfb-rational-p1-projection-scalar-evaluation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.RationalP1
open DiagonalCoefficients CondensedRing

attribute [local irreducible] moduleObjectDerivedPullback moduleObjectDerivedPushforward

/-- Evaluating a scalar after the fixed right projection mate.

Source: the counit projection formula and
CategoryTheory.Adjunction.rightAdjointProjectionMap_rightUnitality in the adopted
projection-map library; blueprint First identity, evaluation of the q trace.
(blueprint: lem-sfb-rational-p1-projection-scalar-evaluation).

Proof: the normalization in projectionMate_existsUnique identifies projectionMateMap
with the native counit projection mate. Apply its naturality square to t : K → 1.
Postcompose by the direct image of M tensor the pullback's oplax unit comparison
and the right unitor. Projection right-unitality identifies the projection at 1
followed by these factors with the right unitor of Rq_* M. The original derived
pullback oplax unit is leftDerivedUpperStarUnitIso.hom. The strong structure was
constructed from this unit isomorphism, so its inverse unit comparison, cached as
secondTraceUnitIso, is the same map. Transfer the calculation through the fixed
native tensor bundle and the representative-normalized projection family.
Before applying this calculation, tensor the given scalar square with M and
postcompose by its right unitor. Combine tensor whiskerings and use functoriality
to replace the compatible scalar functional by the pullback of t and the unit map.
Only functoriality, naturality and right-unitality enter: no trace, diagram,
line object, reference, base-field, or invertibility hypothesis is used. Finally
precompose the equality by the two arbitrary prescribed prefix arrows A and B. -/
theorem projectionMate_scalar_evaluation
    (l : ℕ) [Fact l.Prime] (c : Option (PadicAlgCl.FiniteIntermediateField l))
    (Y : Scheme.{u})
    (M : DerivedCategory (Modules (coefficient l c).X (ProjectiveLine Y)))
    (K : DerivedCategory (Modules (coefficient l c).X Y))
    (S T : DerivedCategory (Modules (coefficient l c).X Y))
    (A : S ⟶ T)
    (B : T ⟶ (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M ⊗ K)
    (V W : DerivedCategory (Modules (coefficient l c).X (ProjectiveLine Y)))
    (b : (moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj K ⟶ V)
    (v : V ⟶ W) (w : W ⟶ 𝟙_ (DerivedCategory (Modules (coefficient l c).X (ProjectiveLine Y))))
    (t : K ⟶ 𝟙_ (DerivedCategory (Modules (coefficient l c).X Y)))
    (ht : b ≫ v ≫ w =
      (moduleObjectDerivedPullback (coefficient l c).X (ProjectiveLine Y ↘ Y)).map t ≫
        (secondTraceUnitIso (coefficient l c).X Y).hom) :
    A ≫ B ≫ projectionMateMap (coefficient l c).X (ProjectiveLine Y ↘ Y) M K ≫
      (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map (M ◁ b) ≫
      (moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).map
        ((M ◁ v) ≫ (M ◁ w) ≫ (ρ_ M).hom) =
      A ≫ B ≫ ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M ◁
      t) ≫
        (ρ_ ((moduleObjectDerivedPushforward (coefficient l c).X (ProjectiveLine Y ↘ Y)).obj M)).hom
      := by sorry

end AlgebraicGeometry.ProEtale.RationalP1
