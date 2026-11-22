module
public import WeilConjectures.AlgebraicGeometry.IndEtaleMapping.IndEtaleDerivedImageHomCounit

set_option autoImplicit false
set_option synthInstance.maxSize 4096
@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Etale.IndEtaleMapping

variable (A : Type (u + 1)) [CommRing A]
variable {X : Scheme.{u}} (K M : DerivedCategoryModule A X)

example (T : Over X) :
    (imageTensorIso A K T).hom.app
      (((ExternalRHom.globalHom A X).obj (op K)).obj (imageValue A M T)) =
    (imageTensorIso A K T).hom.app
      ((fun Y => Y) (((ExternalRHom.globalHom A X).obj (op K)).obj (imageValue A M T))) := by
  have h :
      (imageTensorIso A K T).hom.app
        ((fun Y => Y) (((ExternalRHom.globalHom A X).obj (op K)).obj (imageValue A M T))) =
      (imageTensorIso A K T).hom.app
        (((ExternalRHom.globalHom A X).obj (op K)).obj (imageValue A M T)) := by rfl
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let h ← Lean.Meta.getFVarFromUserName `h
      let actual ← Lean.Meta.inferType h
      let expected ← (← Lean.Elab.Tactic.getMainGoal).getType
      Lean.logInfo m!"matched pair syntactic={actual == expected}"
  exact h

example (T : Over X) :
    (ExternalRHom.constant A T.left ⋙
      CategoryTheory.MonoidalCategory.tensorLeft ((ExternalRHom.pull A T.hom).obj K)).map
        (imageHomIso A M K T).hom =
    (ExternalRHom.constant A T.left ⋙
      CategoryTheory.MonoidalCategory.tensorLeft ((ExternalRHom.pull A T.hom).obj K)).map
        ((fun g => g) (imageHomIso A M K T).hom) := by
  have h :
      (ExternalRHom.constant A T.left ⋙
        CategoryTheory.MonoidalCategory.tensorLeft ((ExternalRHom.pull A T.hom).obj K)).map
          ((fun g => g) (imageHomIso A M K T).hom) =
      (ExternalRHom.constant A T.left ⋙
        CategoryTheory.MonoidalCategory.tensorLeft ((ExternalRHom.pull A T.hom).obj K)).map
          (imageHomIso A M K T).hom := by rfl
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let h ← Lean.Meta.getFVarFromUserName `h
      let actual ← Lean.Meta.inferType h
      let expected ← (← Lean.Elab.Tactic.getMainGoal).getType
      Lean.logInfo m!"map pair syntactic={actual == expected}"
  exact h

end AlgebraicGeometry.Etale.IndEtaleMapping
