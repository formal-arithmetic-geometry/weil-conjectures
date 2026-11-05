/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryProjectionFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FilteredColimit.FunctorCategory

/-!
# Total right derived functors commute with filtered colimits of bounded below complexes

Let `G : C ⥤ D` be a left exact additive functor from a Grothendieck abelian category, and `J` a
small category such that colimits of shape `J` are exact in `C` and in `D` (e.g. `J` filtered),
and such that the classical right derived functors `RᵠG` commute with colimits of shape `J`.
Then for a diagram `F : J ⥤ CochainComplex C ℤ` of complexes uniformly bounded below and a
colimit cocone `c` of `F`, each cohomology functor of the total right derived functor `RG`
commutes with the colimit: `colim Hᵠ(RG(F j)) ≅ Hᵠ(RG(colim F))`
(`CategoryTheory.Functor.isColimit_mapCocone_Q_comp_rightDerivedFunctor_comp_homologyFunctor`).

Indeed, resolve `F` functorially by a diagram `I` of bounded below complexes of injectives
(`CategoryTheory.Functor.exists_quasiIso_injective_of_isStrictlyGE`). As colimits of shape `J` are
exact, `colim F ⟶ colim I` is a quasi-isomorphism; the colimits `colim_j I_j^n` are `G`-acyclic,
`RᵠG` commuting with colimits of shape `J`. So `RG` is computed termwise on the `I_j` and on
`colim I` (`CategoryTheory.Functor.isIso_rightDerivedFunctorUnitQ_of_isStrictlyGE`), and `G`
applied termwise, followed by cohomology, commutes with colimits of shape `J`.
-/

@[expose] public section

universe w

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C D : Type*} [Category.{w} C] [Category* D] [Abelian C] [Abelian D]
  [IsGrothendieckAbelian.{w} C] [HasDerivedCategory C] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions C]
  (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G]

variable {J : Type w} [SmallCategory J] [HasExactColimitsOfShape J C]
  [HasColimitsOfShape J D] [HasExactColimitsOfShape J D]

end CategoryTheory.Functor
