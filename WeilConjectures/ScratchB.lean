module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.AlgebraicGeometry.Sites.Ga
public import WeilConjectures.Mathlib.Topology.Sheaves.Flasque

open CategoryTheory TopologicalSpace

universe u

instance (X : TopCat.{u}) : EssentiallySmall.{u + 1} (Opens X) :=
  have : LocallySmall.{u + 1} (Opens X) :=
    @locallySmall_of_univLE (Opens X) _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

instance (X : TopCat.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall _ _

variable (X : AlgebraicGeometry.Scheme.{u})
  (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1})

#check Sheaf.H F 2
example : EnoughInjectives (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u + 1}) := inferInstance
#check @TopCat.Presheaf.isFlasque_of_epi
#check @CategoryTheory.Sheaf.surjective_map_of_injective
