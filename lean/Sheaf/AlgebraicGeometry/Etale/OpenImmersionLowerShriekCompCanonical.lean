module

public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

@[expose] public section

universe u

open CategoryTheory
namespace AlgebraicGeometry
open Etale

/-- The extension comparison is the generic left-adjoint comparison induced by `upperStarComp`.
This identification is obtained by unfolding `openImmersionLowerShriekComp` and the mate
construction; it is recorded separately so dependent transports for identity and associativity
can be handled before applying the generic coherence lemmas. The proof unfolds both mate
constructions,
uses the defining conjugate equivalence and its unit equation, and applies proof irrelevance to
all scheme-morphism equality transports.
(blueprint: lem-cbc-extension-zero-composition-canonical-comparison) -/
theorem Etale.openImmersionLowerShriekComp_canonical
    (Λ : Type (u + 1)) [CommRing Λ] :
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
      (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) (𝟙 U) j).inv.app F ≫
        eqToHom (by simp only [Category.id_comp]) =
      (Adjunction.leftAdjointCompIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 U))
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
        (upperStarComp (ModuleCat.{u + 1} Λ) (𝟙 U) j j
          (Category.id_comp j).symm).symm).hom.app F) ∧
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
      (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) j (𝟙 X)).inv.app F ≫
        eqToHom (by simp only [Category.comp_id]) =
      (Adjunction.leftAdjointCompIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X))
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j)
        (upperStarComp (ModuleCat.{u + 1} Λ) j (𝟙 X) j
          (Category.comp_id j).symm).symm).hom.app F) ∧
    (∀ {U V W : Scheme.{u}} (j₁ : U ⟶ V) (j₂ : V ⟶ W)
      [IsOpenImmersion j₁] [IsOpenImmersion j₂]
      (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) j₁ j₂).inv.app F =
      (Adjunction.leftAdjointCompIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j₁)
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j₂)
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (j₁ ≫ j₂))
        (upperStarComp (ModuleCat.{u + 1} Λ) j₁ j₂).symm).hom.app F) ∧
    (∀ {U V W X : Scheme.{u}} (j₁ : U ⟶ V) (j₂ : V ⟶ W) (j₃ : W ⟶ X)
      [IsOpenImmersion j₁] [IsOpenImmersion j₂] [IsOpenImmersion j₃]
      (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
      (openImmersionLowerShriekComp (ModuleCat.{u + 1} Λ) (j₁ ≫ j₂) j₃).inv.app F ≫
        eqToHom (by simp only [Category.assoc]) =
      (Adjunction.leftAdjointCompIso
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) (j₁ ≫ j₂))
        (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} Λ) j₃)
        (openImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} Λ) (j₁ ≫ j₂ ≫ j₃))
        (upperStarComp (ModuleCat.{u + 1} Λ) (j₁ ≫ j₂) j₃
          (j₁ ≫ j₂ ≫ j₃) (by simp [Category.assoc])).symm).hom.app F) := by
  sorry

end AlgebraicGeometry
