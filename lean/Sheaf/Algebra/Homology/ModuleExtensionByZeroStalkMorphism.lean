module

public import Sheaf.Algebra.Homology.OpenRestrictionAdjunctionExact
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Topology.Sheaves.Module

/-! # The unit-induced linear stalk morphism

Source: Stacks Project, Sheaves Lemma 00A7 (2), (3).
(blueprint: lem-sc-module-extension-by-zero-stalk-morphism).
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
universe u
noncomputable section
namespace AlgebraicGeometry
/-- The unit induces a natural linear morphism from the restricted stalk to the extension stalk,
with its value on every germ. This asserts construction and the germ formula only.
Source: Stacks Project, Sheaves Lemma 00A7 (2), Lemma 007Z and Modules Lemma 01AK.
(blueprint: lem-sc-module-extension-by-zero-stalk-morphism).

Proof: Apply the module stalk functor to the unit after converting from the slice site to W.
Compose with the restriction-stalk comparison for the underlying abelian sheaf. To prove
linearity, represent a scalar and a vector on a common neighborhood in W, use the linearity
of the unit there and the germ scalar multiplication formula, and transport the scalar by
restrictStalkIso.inv. Every stalk element has such a representative. Naturality follows by
checking germs and using the naturality of the unit. The restriction-stalk germ formula
then gives the displayed identity. This construction does not assert invertibility. -/
theorem exists_moduleExtensionByZero_stalk_morphism (X : RingedSpace.{u}) :
    (∀ (W : Opens X) (x : X) (hx : x ∈ W),
      ∃ e : (W.sheafOfModulesEquivOver (moduleRings X)).functor ⋙
          RingedSpace.moduleStalkFunctor (X.restrict (Opens.isOpenEmbedding W)) ⟨x, hx⟩ ⋙
          ModuleCat.restrictScalars
            (X.toPresheafedSpace.restrictStalkIso (Opens.isOpenEmbedding W) ⟨x, hx⟩).inv.hom ⟶
        (SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W ⋙
          PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)) ⋙
          RingedSpace.moduleStalkFunctor X x,
        ∀ (G : SheafOfModules.{u} ((moduleRings X).over W)) (V : Opens W)
          (hV : (⟨x, hx⟩ : W) ∈ V)
          (s : ((W.sheafOfModulesEquivOver (moduleRings X)).functor.obj G).val.obj (op V)),
          (e.app G) (TopCat.Presheaf.germ (C := Ab.{u})
              (X := (X.restrict (Opens.isOpenEmbedding W)).carrier)
              ((W.sheafOfModulesEquivOver (moduleRings X)).functor.obj G).val.presheaf
              V ⟨x, hx⟩ hV s) =
            TopCat.Presheaf.germ (C := Ab.{u}) (X := X.carrier)
              ((SheafOfModules.extensionByZeroPresheaf.{u} (moduleRings X) W ⋙
                PresheafOfModules.sheafification.{u} (𝟙 (moduleRings X).obj)).obj
                  G).val.presheaf
              ((Opens.isOpenEmbedding W).isOpenMap.functor.obj V) x ⟨⟨x, hx⟩, hV, rfl⟩
              (((Classical.choice (open_restriction_adjunction_exact X W).2.2.2.2).unit.app
                G).val.app
                (op (Over.mk (homOfLE (Set.image_subset_iff.2 (fun y _ => y.2))))) s))
 := by sorry

end AlgebraicGeometry
