/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Sheaf.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.Restrict

/-! # Coherent descent through open restriction

Source: Stacks Project, Tags 08EU and 08FE.
(blueprint: lem-pc-open-restriction-tensor-counit-descent).
-/

@[expose] public section

universe u w
open CategoryTheory MonoidalCategory
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
variable [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
variable [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
variable [HasDerivedCategory.{u}
  (SheafOfModules.{u} (moduleRings (f ⁻¹ᵁ U).toScheme.toRingedSpace))]
variable [HasDerivedCategory.{u}
  (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]


/-- Tensor comparison and counit descend together before taking an adjunction transpose.
Source: Stacks Project, Tag 08EU, first sentence of proof; Tag 08FE.
Proof: construct rhoX and rhoY naturally on K-flat total tensor models, using exact
restriction and its compatibility with tensor and totalization; descend these maps
and their inverses to the specified small derived localizations. Open restriction is
a localization, as is its product with itself. Conjugate the restriction of t by rhoX,
rhoY and alpha to obtain an isomorphism between the restrictions of the two local
bifunctors. Full faithfulness of precomposition with this product localization lifts
it uniquely to s. Its factorization identity gives compatibility on every pair of
global inputs. The assumed Hom-equivalence compatibility
identifies the restricted counit of p with that of q: take the source object to be
the direct image of B and the input morphism to be p's counit, whose p-transpose
is the identity, and use injectivity of q's Hom equivalence.
Combine this counit identity with the tensor naturality square. Their composite is
the displayed identity between morphisms BEFORE transposing along q. Thus this is
the tensor/counit step, not an assertion comparing projection mates as arrows.
No quasi-coherence or invertibility of a projection mate is used. All localization
counits and K-flat restriction comparisons apply unchanged when the open is empty.
(blueprint: lem-pc-open-restriction-tensor-counit-descent). -/
theorem exists_openRestriction_tensor_counit_descent
    (p : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (t : tensor (schemeDerivedCategory Y) ⋙ derivedPullback f ≅
      (derivedPullback f).prod (derivedPullback f) ⋙ tensor (schemeDerivedCategory X)) :
    let rX := (schemeOpenRestriction X (f ⁻¹ᵁ U)).mapDerivedCategory
    let rY := (schemeOpenRestriction Y U).mapDerivedCategory
    ∀ (q : derivedPullback (f ∣_ U) ⊣ schemeDerivedDirectImage (f ∣_ U))
      (alpha : derivedPullback f ⋙ rX ≅ rY ⋙ derivedPullback (f ∣_ U))
      (beta : schemeDerivedDirectImage f ⋙ rY ≅ rX ⋙ schemeDerivedDirectImage (f ∣_ U)),
    (∀ (A : schemeDerivedCategory Y) (B : schemeDerivedCategory X)
      (v : (derivedPullback f).obj A ⟶ B),
      rY.map (p.homEquiv A B v) ≫ beta.hom.app B =
        q.homEquiv (rY.obj A) (rX.obj B) (alpha.inv.app A ≫ rX.map v)) →
    ∃ (s : tensor (schemeDerivedCategory U.toScheme) ⋙ derivedPullback (f ∣_ U) ≅
        (derivedPullback (f ∣_ U)).prod (derivedPullback (f ∣_ U)) ⋙
          tensor (schemeDerivedCategory (f ⁻¹ᵁ U).toScheme))
      (rhoY : tensor (schemeDerivedCategory Y) ⋙ rY ≅
        rY.prod rY ⋙ tensor (schemeDerivedCategory U.toScheme))
      (rhoX : tensor (schemeDerivedCategory X) ⋙ rX ≅
        rX.prod rX ⋙ tensor (schemeDerivedCategory (f ⁻¹ᵁ U).toScheme)),
      ∀ (A : schemeDerivedCategory Y) (B : schemeDerivedCategory X),
        alpha.inv.app (A ⊗ (schemeDerivedDirectImage f).obj B) ≫
          rX.map (t.hom.app (A, (schemeDerivedDirectImage f).obj B) ≫
            (𝟙 ((derivedPullback f).obj A) ⊗ₘ p.counit.app B)) ≫
          (rhoX.hom.app ((derivedPullback f).obj A, B) ≫
            (alpha.hom.app A ⊗ₘ 𝟙 (rX.obj B))) =
        (derivedPullback (f ∣_ U)).map (rhoY.hom.app (A, (schemeDerivedDirectImage f).obj B) ≫
          (𝟙 (rY.obj A) ⊗ₘ beta.hom.app B)) ≫
          (s.hom.app (rY.obj A, (schemeDerivedDirectImage (f ∣_ U)).obj (rX.obj B)) ≫
            (𝟙 ((derivedPullback (f ∣_ U)).obj (rY.obj A)) ⊗ₘ
              q.counit.app (rX.obj B))) := by sorry

end AlgebraicGeometry
