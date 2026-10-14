module
public import Sheaf.Algebra.Homology.AffineDerivedPushforwardSheafEdgeCanonical
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
/-- The affine sheaf edge transformation exists, with its witness pinned to the canonical inverse
of the unique reverse cycle-class comparison on K-injective representatives.
Source: Stacks Project, Tags 0AVW and
08D4. (blueprint: lem-pc-affine-derived-pushforward-sheaf-edge-existence).
The construction uses the cycle-class comparison in a K-injective resolution on the
basis of affine opens and glues these compatible maps. -/
theorem exists_affineDerivedPushforwardSheafEdge_existence
    (A B : Type u) [CommRing A] [CommRing B] (φ : B →+* A) (i : ℤ) :
  ∃ ε : ((schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) i ⋙
      RingedSpace.moduleDirectImage (Spec.map (CommRingCat.ofHom φ)).toLRSHom.toShHom ⟶
    (schemeDerivedQCohProperty (Spec (.of A))).ι ⋙
      schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φ)) ⋙
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i),
    ε = affineDerivedPushforwardSheafEdge_canonical A B φ i := by
  exact ⟨affineDerivedPushforwardSheafEdge_canonical A B φ i, rfl⟩
end AlgebraicGeometry
