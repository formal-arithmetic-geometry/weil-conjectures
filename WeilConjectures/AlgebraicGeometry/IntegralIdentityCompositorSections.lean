/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralInverseImageComparisonComposition

/-! # The sectionwise identity compositor

Source: Stacks Tag 03D6, the identity normalization in the Weil-structures paragraph.
(blueprint: lem-sf-integral-identity-compositor-sections)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective in
/-- Section normalization forces the identity compositor equation.
Source: Stacks Tag 03D6, Weil-structures identity normalization.
(blueprint: lem-sf-integral-identity-compositor-sections).
Proof: evaluate on an arbitrary module and section. On the left the compositor
restricts along the site composition map and r then restricts along the inverse
site identity map. On the right inverse image of e is restriction along the
identity map at the transported object, and e restricts once more. Both composites
are the same morphism of the Pro-etale over-category: each is the identity on the
underlying scheme and has the required structure equation. Functoriality of the
module presheaf identifies the two section maps. Extensionality of linear maps,
presheaf morphisms, sheaf morphisms and natural transformations gives the result. -/
theorem integralIdentityCompositorSections
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (X : Scheme.{u})
    (e : inverseImageIntegralModules l E (𝟙 X) ≅ 𝟭 (integralTowerModules l E X))
    (r : inverseImageIntegralModules l E ((𝟙 X) ≫ (𝟙 X)) ≅
      𝟭 (integralTowerModules l E X))
    (he : ∀ (M : integralTowerModules l E X) (U : X.ProEt)
      (x : ((inverseImageIntegralModules l E (𝟙 X)).obj M).val.obj (op U)),
      (e.hom.app M).val.app (op U) x =
        M.val.map ((MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ X (𝟙 X)
          rfl).inv.app U).op x)
    (hr : ∀ (M : integralTowerModules l E X) (U : X.ProEt)
      (x : ((inverseImageIntegralModules l E ((𝟙 X) ≫ (𝟙 X))).obj M).val.obj (op U)),
      (r.hom.app M).val.app (op U) x =
        M.val.map ((MorphismProperty.Over.mapId (P := @WeaklyEtale) ⊤ X
          ((𝟙 X) ≫ (𝟙 X)) (Category.id_comp (𝟙 X))).inv.app U).op x) :
    (integralInverseImageComposition l E (𝟙 X) (𝟙 X)).hom ≫ r.hom =
      (Functor.whiskerRight e.hom (inverseImageIntegralModules l E (𝟙 X)) ≫
        (Functor.leftUnitor (inverseImageIntegralModules l E (𝟙 X))).hom) ≫ e.hom := by sorry

end WeilConjectures
