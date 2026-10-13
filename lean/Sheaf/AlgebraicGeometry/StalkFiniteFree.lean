module
public import Sheaf.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules
/-- Finite locally free sheaves have finite free stalk modules.
Source: Stacks Project, Tag 01C6, Definition 17.14.1(2).

Proof: Choose a finite trivializing frame on an open neighborhood U of x.
Take germs of its basis sections and coordinate projections at x. Every
stalk element has a representative on a smaller neighborhood inside U;
the finite coordinate decomposition there gives the corresponding
expansion of its germ. The coordinate projections give uniqueness of
coefficients. Thus these germs form a finite basis over O_{X,x}, establishing
Module.Free and Module.Finite. An empty frame yields the zero module; there
is no assertion to check if X has no points.
(blueprint: lem-sc-stalk-finite-free-of-finite-locally-free) -/
theorem stalk_isFiniteFree_of_isFiniteLocallyFree
    {X : Scheme.{u}} (M : X.Modules) [M.IsFiniteLocallyFree] (x : X) :
    Module.Free (X.presheaf.stalk x)
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj M) ∧
      Module.Finite (X.presheaf.stalk x)
        ((RingedSpace.moduleStalkFunctor X.toRingedSpace x).obj M) := by
  sorry
end AlgebraicGeometry.Scheme.Modules
