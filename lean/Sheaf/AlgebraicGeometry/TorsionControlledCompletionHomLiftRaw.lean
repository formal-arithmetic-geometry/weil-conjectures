module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The underlying morphism-lifting part of Tag 0889(1).  On an affine cover,
the torsion hypotheses make the arrows isomorphisms after localization; the
localized comparison maps descend through the formal gluing complex and glue
to a coherent morphism.

Proof: Construct the localized comparison maps, descend them by formal gluing exactness,
and glue the local morphisms over the affine cover.
(blueprint: lem-weil-pbc-torsion-controlled-completion-hom-lift-raw) -/
theorem torsionControlled_completion_hom_lift_raw
    {X : Scheme.{u}} [IsNoetherian X] (J : X.IdealSheafData)
    (H F F' : CoherentModules X) (a : F ⟶ H) (a' : F' ⟶ H)
    (ha : (∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (kernel a.hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (cokernel a.hom))))
    (ha' : (∃ s : ℕ, 1 ≤ s ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (kernel a'.hom)) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι s).2
        (cokernel a'.hom)))) :
    ∃ g : F ⟶ F', g ≫ a' = a := by sorry

end AlgebraicGeometry
