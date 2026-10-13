module

public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.Topology.Sheaves.Module
public import Mathlib.Geometry.RingedSpace.Stalks

@[expose] public section
open CategoryTheory TopologicalSpace Opposite
universe u
noncomputable section
namespace AlgebraicGeometry

/-- Componentwise linear stalk comparison for restriction, with its germ formula.
Source: Stacks Project, Sheaves Section 6.31, Lemma 6.31.1 (3).
(blueprint: new-module-restriction-stalk-components).

Proof: represent a restricted stalk element by a germ on a neighborhood in the open,
then send it to the germ on its image in the ambient space.  The additive stalk
comparison is induced by the final neighborhood functor.  The germ scalar
multiplication formula, applied on a common neighborhood, shows that this map is
linear after transporting scalars along the inverse restriction-stalk ring map.
-/
theorem exists_moduleRestrictionStalk_components (X : RingedSpace.{u}) (W : Opens X)
    (x : X) (hx : x ∈ W) :
    ∃ c : ∀ F : SheafOfModules.{u} (moduleRings X),
      (ModuleCat.restrictScalars
          (X.toPresheafedSpace.restrictStalkIso W.isOpenEmbedding ⟨x, hx⟩).inv.hom).obj
        ((RingedSpace.moduleStalkFunctor (X.restrict W.isOpenEmbedding) ⟨x, hx⟩).obj
          ((W.sheafOfModulesEquivOver (moduleRings X)).functor.obj
            ((SheafOfModules.overFunctor (moduleRings X) W).obj F))) ⟶
        (RingedSpace.moduleStalkFunctor X x).obj F,
      ∀ (F : SheafOfModules.{u} (moduleRings X)) (V : Opens W)
        (hV : (⟨x, hx⟩ : W) ∈ V)
        (s : F.val.obj (op (W.isOpenEmbedding.isOpenMap.functor.obj V))),
        (c F) (TopCat.Presheaf.germ (C := Ab.{u})
          (X := (X.restrict W.isOpenEmbedding).carrier)
          ((W.sheafOfModulesEquivOver (moduleRings X)).functor.obj
            ((SheafOfModules.overFunctor (moduleRings X) W).obj F)).val.presheaf
          V ⟨x, hx⟩ hV s) =
        TopCat.Presheaf.germ (C := Ab.{u}) (X := X.carrier) F.val.presheaf
          (W.isOpenEmbedding.isOpenMap.functor.obj V) x ⟨⟨x, hx⟩, hV, rfl⟩ s := by
  sorry

end AlgebraicGeometry
end
