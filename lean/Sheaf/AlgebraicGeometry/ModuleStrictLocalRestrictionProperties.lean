module

public import Sheaf.AlgebraicGeometry.ModuleStrictLocalSectionRestriction

/-! # Exactness and descent for module-valued strict-local restriction
Source: Stacks Tags 03Q9 and 03QO
(blueprint: lem-pur-module-strict-local-restriction-properties).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

/-- Exact module stalks, exact strict-local sections, and unique descent of the
specified module restrictions from the pointed affine-neighbourhood diagram.
Source: Stacks Tags 03Q9 and 03QO
(blueprint: lem-pur-module-strict-local-restriction-properties).
Proof: filtered colimits of modules commute with finite limits, and the stalk is that
filtered colimit. For strict-local sections, forget scalars: local surjectivity and a
section of every etale cover through the closed point give surjectivity on sections;
kernels are sectionwise, hence sections are exact. The affine pointed representatives
are cofinal in the geometric stalk diagram. The inverse-image unit and the limit legs
make the displayed section restrictions a cocone. Colimit descent supplies r, the
colimit equations supply its germ identities, and colimit extensionality supplies its
uniqueness and naturality in the coefficient sheaf. This argument uses the actual
small strict-henselization model and imposes no finiteness condition on the base.
-/
theorem moduleStrictLocalRestriction_properties (A : Type (u + 1)) [CommRing A]
    {B : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ B) :
    PreservesFiniteLimits
      ((Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} A)) ∧
    PreservesFiniteColimits
      (Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        (ModuleCat.{u + 1} A)) ∧
    ∃! r : (Scheme.pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} A) ⟶
      upperStar (ModuleCat.{u + 1} A) (Scheme.strictHenselizationStructuralMap s) ⋙
        Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology (ModuleCat.{u + 1} A),
      ∀ (F : Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} A))
        (j : SmallModel.{u} (Scheme.strictHenselizationNeighbourhoods s)),
        (Scheme.pointSmallEtale s).toPresheafFiber
          ((Scheme.AffineEtale.Spec B).obj
            ((equivSmallModel.{u}
              (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).1)
          ((equivSmallModel.{u}
            (Scheme.strictHenselizationNeighbourhoods s)).inverse.obj j).2 F.obj ≫ r.app F =
          moduleStrictLocalSectionRestriction A s F j := by
  sorry

end AlgebraicGeometry.Etale
