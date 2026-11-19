-- Prints the goal and inferred helper type immediately before their Kernel conversion.
module
public import WeilConjectures.AlgebraicGeometry.IndEtaleMapping.IndEtaleDerivedImageHomCounit
public meta import HeadAuditTools
set_option maxHeartbeats 200000
set_option pp.explicit false
set_option pp.proofs false
set_option pp.universes false
set_option linter.unusedTactic false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.Etale.IndEtaleMapping

variable (A : Type (u + 1)) [CommRing A]
def regularDerivedCategoryModule {X : Scheme.{u}} : Type (u + 2) :=
  DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
variable {X : Scheme.{u}} (K M : regularDerivedCategoryModule A (X := X))

example (T : Over X) :
    (ExternalRHom.constant A T.left ⋙
      CategoryTheory.MonoidalCategory.tensorLeft ((ExternalRHom.pull A T.hom).obj K)).map
        (imageHomIso A M K T).hom ≫
      (ExternalRHom.globalAdjunction A ((ExternalRHom.pull A T.hom).obj K)).counit.app
        ((ExternalRHom.pull A T.hom).obj M) =
      (imageTensorIso A K T).hom.app
        (((ExternalRHom.globalHom A X).obj (op K)).obj (imageValue A M T)) ≫
      ((ExternalRHom.globalAdjunction A K).comp
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) T.hom)).counit.app
          ((ExternalRHom.pull A T.hom).obj M) := by
  have h := conjugateEquiv_counit
    ((ExternalRHom.globalAdjunction A K).comp
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) T.hom))
    (ExternalRHom.globalAdjunction A ((ExternalRHom.pull A T.hom).obj K))
    (imageTensorIso A K T).hom ((ExternalRHom.pull A T.hom).obj M)
  run_tac do Lean.Elab.Tactic.withMainContext do
    let h ← Lean.Meta.getFVarFromUserName `h
    let actual ← Lean.Meta.inferType h
    let expected ← (← Lean.Elab.Tactic.getMainGoal).getType
    HeadAuditTools.pair actual expected
  sorry

end AlgebraicGeometry.Etale.IndEtaleMapping
