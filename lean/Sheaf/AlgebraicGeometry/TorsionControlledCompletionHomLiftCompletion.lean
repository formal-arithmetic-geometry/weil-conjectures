module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

/-- The completion compatibility part of Tag 0889(1).  The affine comparison
maps used in the raw lift agree with the prescribed completed map; exactness
of the formal gluing complex and the sheaf gluing lemma preserve this equality.
Proof: Compare the localized maps with the prescribed completed map and use exactness
and sheaf gluing to descend the equality.
(blueprint: lem-weil-pbc-torsion-controlled-completion-hom-lift-completion)
-/
theorem torsionControlled_completion_hom_lift_completion
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
        (cokernel a'.hom))))
    (θ : (completion X J).obj F ⟶ (completion X J).obj F')
    (hθ : θ ≫ (completion X J).map a' = (completion X J).map a)
    (g : F ⟶ F') (hg : g ≫ a' = a) :
    (completion X J).map g = θ := by sorry

end AlgebraicGeometry
