module

public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.AlgebraicGeometry.GrothendieckExistenceEasyTorsionTriple
import Sheaf.AlgebraicGeometry.GrothendieckExistenceEasyFromExists
import Sheaf.AlgebraicGeometry.CompletionIsogenyFromHomLift

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
-- The previous signature omitted the ideal-power-torsion
-- condition on a and a'. With I = O_X completion is zero, so arbitrary coherent
-- modules would be uniquely isomorphic. The corrected signature restores Stacks 0889.
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
        (∃ t : ℕ, 1 ≤ t ∧
          IsZero (Scheme.idealModuleProduct
            (Scheme.idealSheafPower I.toModulesι t).2 (kernel a.hom)) ∧
          IsZero (Scheme.idealModuleProduct
            (Scheme.idealSheafPower I.toModulesι t).2 (cokernel a.hom))) ∧
        α = β.hom ≫ (completion X I).map a ∧
        ∀ (H' : CoherentModules X) (a' : H' ⟶ G)
          (β' : F ≅ (completion X I).obj H'),
          (∃ t : ℕ, 1 ≤ t ∧
            IsZero (Scheme.idealModuleProduct
              (Scheme.idealSheafPower I.toModulesι t).2 (kernel a'.hom)) ∧
            IsZero (Scheme.idealModuleProduct
              (Scheme.idealSheafPower I.toModulesι t).2 (cokernel a'.hom))) →
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
        (∃ t : ℕ, 1 ≤ t ∧
          IsZero (Scheme.idealModuleProduct
            (Scheme.idealSheafPower I.toModulesι t).2 (kernel a.hom)) ∧
          IsZero (Scheme.idealModuleProduct
            (Scheme.idealSheafPower I.toModulesι t).2 (cokernel a.hom))) ∧
        α = (completion X I).map a ≫ β.hom ∧
        ∀ (H' : CoherentModules X) (a' : G ⟶ H')
          (β' : (completion X I).obj H' ≅ F),
          (∃ t : ℕ, 1 ≤ t ∧
            IsZero (Scheme.idealModuleProduct
              (Scheme.idealSheafPower I.toModulesι t).2 (kernel a'.hom)) ∧
            IsZero (Scheme.idealModuleProduct
              (Scheme.idealSheafPower I.toModulesι t).2 (cokernel a'.hom))) →
          α = (completion X I).map a' ≫ β'.hom →
          ∃! γ : H ≅ H',
            a ≫ γ.hom = a' ∧
              (completion X I).map γ.hom ≫ β'.hom = β.hom) := by
  let C := completion X I
  have hexFrom := grothendieckExistenceEasy_exists_from X I G F
  have liftFrom := completion_isogeny_from_hom_lift X I
  constructor
  · intro α hα
    obtain ⟨H, a, β, hβ, ha, unique⟩ :=
      grothendieckExistenceEasy_torsionTriple I G F α hα
    refine ⟨H, a, β, ha, hβ, ?_⟩
    intro H' a' β' ha' hβ'
    exact unique H' a' β' hβ' ha'
  · intro α hα
    obtain ⟨H, a, β, ha, hβ⟩ := hexFrom α hα
    refine ⟨H, a, β, ha, hβ, ?_⟩
    intro H' a' β' ha' hβ'
    let θ := β.hom ≫ β'.inv
    let θ' := β'.hom ≫ β.inv
    have hθ : C.map a ≫ θ = C.map a' := by
      dsimp [θ, C]
      rw [← Category.assoc, ← hβ, hβ']
      simp
    have hθ' : C.map a' ≫ θ' = C.map a := by
      dsimp [θ', C]
      rw [← Category.assoc, ← hβ', hβ]
      simp
    obtain ⟨f, hf, uf⟩ := liftFrom G H H' a a' ha ha' θ hθ
    obtain ⟨g, hg, _⟩ := liftFrom G H' H a' a ha' ha θ' hθ'
    have hfg : f ≫ g = 𝟙 H := by
      obtain ⟨_, _, unique⟩ := liftFrom G H H a a ha ha (𝟙 _) (by simp)
      apply (unique (f ≫ g) ?_).trans (unique (𝟙 H) (by simp)).symm
      constructor
      · rw [← Category.assoc, hf.1, hg.1]
      · rw [C.map_comp, hf.2, hg.2]
        simp [θ, θ', Category.assoc, C]
    have hgf : g ≫ f = 𝟙 H' := by
      obtain ⟨_, _, unique⟩ := liftFrom G H' H' a' a' ha' ha' (𝟙 _) (by simp)
      apply (unique (g ≫ f) ?_).trans (unique (𝟙 H') (by simp)).symm
      constructor
      · rw [← Category.assoc, hg.1, hf.1]
      · rw [C.map_comp, hg.2, hf.2]
        simp [θ, θ', Category.assoc, C]
    let e : H ≅ H' := ⟨f, g, hfg, hgf⟩
    refine ⟨e, ⟨hf.1, ?_⟩, ?_⟩
    · change C.map f ≫ β'.hom = β.hom
      rw [hf.2]
      simp [θ, Category.assoc]
    · intro δ hδ
      apply Iso.ext
      change δ.hom = f
      apply uf
      refine ⟨hδ.1, ?_⟩
      calc
        C.map δ.hom = (C.map δ.hom ≫ β'.hom) ≫ β'.inv := by simp
        _ = θ := by rw [hδ.2]

end AlgebraicGeometry
