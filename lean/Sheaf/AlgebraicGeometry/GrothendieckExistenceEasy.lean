module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
public import Sheaf.AlgebraicGeometry.CoherentFormalModuleAnnihilated

/-!
# Easy algebraization of formal coherent modules

Source: Stacks Project, Cohomology of Schemes, Lemma 0889 (blueprint:
lem-weil-pbc-grothendieck-existence-easy).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Easy algebraization of formal coherent modules up to ideal-power torsion.
Source: Stacks Project, Cohomology of Schemes, Lemma 0889, lines 6487 and 6504--6550
(blueprint: lem-weil-pbc-grothendieck-existence-easy).
The proof follows the node's restriction to Noetherian affine opens, affine dictionary,
formal gluing existence and uniqueness, and gluing of the resulting triples.
-/
theorem grothendieckExistenceEasy (X : Scheme.{u}) [IsNoetherian X]
    (I : X.IdealSheafData) (G : CoherentModules X)
    (F : CoherentFormalModule X I) :
    (∀ (α : F ⟶ (completion X I).obj G),
      (∃ t : ℕ, 1 ≤ t ∧ ∀ n : ℕ,
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower I.toModulesι t).2
          (kernel (α.hom.app (op n)))) ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower I.toModulesι t).2
          (cokernel (α.hom.app (op n))))) →
      ∃ (H : CoherentModules X) (a : H ⟶ G)
        (β : F ≅ (completion X I).obj H),
        α = β.hom ≫ (completion X I).map a ∧
        ∀ (H' : CoherentModules X) (a' : H' ⟶ G)
          (β' : F ≅ (completion X I).obj H'),
          α = β'.hom ≫ (completion X I).map a' →
          ∃! γ : H ≅ H',
            γ.hom ≫ a' = a ∧
              β.hom ≫ (completion X I).map γ.hom = β'.hom) ∧
    (∀ (α : (completion X I).obj G ⟶ F),
      (∃ t : ℕ, 1 ≤ t ∧ ∀ n : ℕ,
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower I.toModulesι t).2
          (kernel (α.hom.app (op n)))) ∧
        IsZero (Scheme.idealModuleProduct
          (Scheme.idealSheafPower I.toModulesι t).2
          (cokernel (α.hom.app (op n))))) →
      ∃ (H : CoherentModules X) (a : G ⟶ H)
        (β : (completion X I).obj H ≅ F),
        α = (completion X I).map a ≫ β.hom ∧
        ∀ (H' : CoherentModules X) (a' : G ⟶ H')
          (β' : (completion X I).obj H' ≅ F),
          α = (completion X I).map a' ≫ β'.hom →
          ∃! γ : H ≅ H',
            a ≫ γ.hom = a' ∧
              (completion X I).map γ.hom ≫ β'.hom = β.hom):= by
  sorry

end AlgebraicGeometry
