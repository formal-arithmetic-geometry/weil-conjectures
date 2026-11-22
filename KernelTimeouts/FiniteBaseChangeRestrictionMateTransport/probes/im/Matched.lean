module
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData

set_option autoImplicit false
@[expose] public noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace SheafOfModules.OpenTensorNormalization

example (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t)
    (e : FiniteComparisons A o) (N : FiniteModules A X) :
    e.pullU_pin.ordinary.hom.app
        ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).obj N) ≫
      o.gUPull.ordinary.map (e.open_pin.star.hom.app N) ≫
      o.ordinaryTheta.inv.app (e.realizeX.equivalence.functor.obj N) =
    e.pullU_pin.ordinary.hom.app
        ((fun Y => Y) ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).obj N)) ≫
      o.gUPull.ordinary.map (e.open_pin.star.hom.app N) ≫
      o.ordinaryTheta.inv.app (e.realizeX.equivalence.functor.obj N) := by
  have h :
      e.pullU_pin.ordinary.hom.app
          ((fun Y => Y) ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).obj N)) ≫
        o.gUPull.ordinary.map (e.open_pin.star.hom.app N) ≫
        o.ordinaryTheta.inv.app (e.realizeX.equivalence.functor.obj N) =
      e.pullU_pin.ordinary.hom.app
          ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).obj N) ≫
        o.gUPull.ordinary.map (e.open_pin.star.hom.app N) ≫
        o.ordinaryTheta.inv.app (e.realizeX.equivalence.functor.obj N) := by rfl
  run_tac do
    Lean.Elab.Tactic.withMainContext do
      let h ← Lean.Meta.getFVarFromUserName `h
      let actual ← Lean.Meta.inferType h
      let expected ← (← Lean.Elab.Tactic.getMainGoal).getType
      Lean.logInfo m!"matched pair syntactic={actual == expected}"
  exact h

end SheafOfModules.OpenTensorNormalization
