module

public import Sheaf.AlgebraicGeometry.FiniteLocallyFreeTensorUnit
public import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- The primal base-change map for a pulled-back finite locally free module is invertible.
Source: Stacks Project, Tag 0BDP, projection-formula paragraph.
(blueprint: lem-sc-picard-pullback-base-change-primal)
The proof uses the finite-locally-free projection formula and the adjoint definition
of the base-change map; local frames identify it with the identity map. -/
theorem picard_pullback_base_change_primal {X S T : Scheme.{u}}
    (f : X ⟶ S)
    (hO : ∀ {T' : Scheme.{u}} (g' : T' ⟶ S),
      IsIso ((Classical.choose
        (Modules.exists_tensorPullbackAdjunction (pullback.snd f g'))).unit.app
          (SheafOfModules.unit T'.ringCatSheaf)))
    (E : X.Modules) [E.IsFiniteLocallyFree] (g : T ⟶ S) (N : T.Modules) [N.IsFiniteLocallyFree]
    (e : Nonempty ((Modules.tensorPullback (pullback.fst f g)).obj E ≅
      (Modules.tensorPullback (pullback.snd f g)).obj N))
    {T' : Scheme.{u}} (h : T' ⟶ T) :
      IsIso (Modules.moduleBaseChangeMap (pullback.snd f g)
        (pullback.snd (pullback.snd f g) h) h (pullback.fst (pullback.snd f g) h)
        pullback.condition ((Modules.tensorPullback (pullback.fst f g)).obj E)) := by sorry
end AlgebraicGeometry.Scheme
