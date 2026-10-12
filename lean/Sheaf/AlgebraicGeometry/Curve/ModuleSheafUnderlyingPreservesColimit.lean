module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/--
The sheaf-level forgetful functor from constant-ring module sheaves to abelian
sheaves preserves colimits of any fixed diagram.  This is the bridge needed to
transport a module-sheaf colimit cocone to the underlying abelian sheaves.
Source: Stacks Project, Tags 03CO and 03CY.
(blueprint: lem-pbc-u2-module-sheaf-underlying-preserves-colimit)

The proof forms the presheaf colimit sectionwise, uses preservation of colimits
by the module forgetful functor, and identifies module and abelian sheafification
after forgetting scalars.  The remaining categorical comparison is deferred.
-/
theorem moduleSheaf_underlying_preserves_colimit
    {X : Scheme.{u}} {Λ : Type (u + 1)} [CommRing Λ]
    {A : Type (u + 1)} [SmallCategory A]
    {D : A ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} :
    PreservesColimit D (sheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})) := by
  sorry

end AlgebraicGeometry.Scheme
