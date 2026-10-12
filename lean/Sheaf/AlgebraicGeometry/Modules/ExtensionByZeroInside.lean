module

public import Sheaf.CategoryTheory.ExtensionByZeroPresheaf
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Stalk
import Sheaf.Topology.PresheafModuleStalkFunctor

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

/-- The unit identifies inside-U stalks, linearly and naturally.
Source: Stacks Project, Sheaves, Lemma 00A7 (3).
(blueprint: new-extension-by-zero-inside-stalk)

Neighbourhoods contained in the open are cofinal at a point of the open, so the
stalk of the extension is the input stalk.  The unit and restriction stalk
isomorphism therefore give an isomorphism; the construction is semilinear and
natural in the input sheaf. -/
theorem module_extensionByZero_inside_stalk (X : Scheme.{u}) (U : X.Opens) :
    let R := X.ringCatSheaf
    let P := SheafOfModules.extensionByZeroPresheaf.{u} R U
    let L := P ⋙ PresheafOfModules.sheafification (𝟙 R.obj)
    ∀ adj : L ⊣ SheafOfModules.overFunctor R U,
      let t : ∀ (F : SheafOfModules.{u} (R.over U)) (x : U),
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
              ((toPresheaf U.toScheme).obj ((overEquiv U).functor.obj F)) ⟶
            (toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
              (U.ι x)).obj (L.obj F) := fun F x =>
        (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            ((toPresheaf U.toScheme).map ((overEquiv U).functor.map (adj.unit.app F) ≫
              (overFunctorEquiv U).hom.app (L.obj F))) ≫
          (restrictStalkNatIso U.ι x).hom.app (L.obj F)
      (∀ (F : SheafOfModules.{u} (R.over U)) (x : U),
        letI : Module (U.toScheme.presheaf.stalk x)
            (((overEquiv U).functor.obj F).presheaf.stalk x) :=
          inferInstanceAs (Module (U.toScheme.presheaf.stalk x)
          ↑(TopCat.Presheaf.stalk ((overEquiv U).functor.obj F).val.presheaf x))
        letI : Module (X.presheaf.stalk (U.ι x))
            ((toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u}
              (U.ι x)).obj (L.obj F)) :=
          inferInstanceAs (Module (X.presheaf.stalk (U.ι x))
          ↑(TopCat.Presheaf.stalk (L.obj F).val.presheaf (U.ι x)))
        IsIso (t F x) ∧
          ∀ (r : X.presheaf.stalk (U.ι x))
            (s : ((overEquiv U).functor.obj F).presheaf.stalk x),
            t F x ((U.ι.stalkMap x) r • s) = r • t F x s) ∧
      (∀ (F F' : SheafOfModules.{u} (R.over U)) (α : F ⟶ F') (x : U),
        t F x ≫ (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (U.ι x)).map
            ((toPresheaf X).map (L.map α)) =
          (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            ((toPresheaf U.toScheme).map ((overEquiv U).functor.map α)) ≫ t F' x) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
