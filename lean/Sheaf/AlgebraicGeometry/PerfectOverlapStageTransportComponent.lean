/- Copyright (c) 2026 The SHEAF contributors. -/
module

public import Sheaf.AlgebraicGeometry.PerfectOverlapStageTransport

/-! # Component of the constructed stage transport -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local irreducible] derivedPullback perfectHomComposition
attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
/-- Component equation for fixed cartesian stage transport.
Source: Stacks Project, Tag 0D5S. Evaluate its explicit constructor.
(blueprint: lem-pc-perfect-overlap-stage-transport-component). -/
theorem perfectOverlapStageTransport_hom_app
    {X Y K C T S : Scheme.{u}}
    (g : X ⟶ Y) (f : K ⟶ Y)
    (pX : X ⟶ C) (pK : K ⟶ T) (pY : Y ⟶ S)
    (b : C ⟶ S) (q : T ⟶ S)
    (hg : IsPullback g pX pY b) (hf : IsPullback f pK pY q)
    (U V : Y.Opens)
    (r : (g ⁻¹ᵁ (U ⊓ V)).toScheme ⟶ (f ⁻¹ᵁ (U ⊓ V)).toScheme)
    (m : pullback ((U ⊓ V).ι ≫ pY) b ⟶ pullback ((U ⊓ V).ι ≫ pY) q)
    (hmap :
      ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert hg).isoPullback.inv ≫ r =
        m ≫ ((isPullback_morphismRestrict f (U ⊓ V)).paste_vert hf).isoPullback.inv)
    (A : schemeDerivedCategory (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V).toScheme) :
    (perfectOverlapStageTransport g f pX pK pY b q hg hf U V r m hmap).hom.app A =
      (perfectOverlapDerivedPullbackTransport r
        ((isPullback_morphismRestrict g (U ⊓ V)).paste_vert hg).isoPullback
        ((isPullback_morphismRestrict f (U ⊓ V)).paste_vert hf).isoPullback
        m hmap).hom.app A := by
  unfold perfectOverlapStageTransport
  simp only [Scheme.Hom.preimage_inf]
  rfl

end AlgebraicGeometry
