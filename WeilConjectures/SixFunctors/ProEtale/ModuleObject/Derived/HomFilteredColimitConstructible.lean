/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedTriangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomFilteredColimitBase
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.HomFilteredColimitClosed

/-!
# Continuity of `Hom` out of a constructible sheaf

Blueprint `sk-lem-constructible-ext-continuity`. Let `Λ` be a commutative condensed ring such that
`Λ_X` is flat on every scheme `X`, and such that on every scheme with noetherian underlying space,
`Hom(L[0], -[q])` commutes with filtered colimits of module objects for every pro-étale locally
finitely presented (lisse) module object `L`. Then on a scheme `T` with noetherian underlying space
the same holds for every constructible module object `M`
(`homCommutesWithFilteredColimits_singleFunctor_of_isConstructibleModuleObject`).

The proof is the noetherian induction of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleLisseDevissage`
(not imported, to stay below the localizing subcategories in the import hierarchy):
a constructible sheaf `G` on a closed subscheme `c : D ⟶ T` is split, along a nonempty open `V`
of `D` contained in a stratum, by the open–closed triangle `j_! Lj^* G ⟶ G ⟶ Ri_* Li^* G ⟶`
into the extension by zero of a lisse sheaf and a sheaf supported on a smaller closed subset. The
class of objects whose morphisms commute with filtered colimits is closed under extensions
(`DerivedCategory.HomCommutesWithFilteredColimits.ext₂`), under `j_!` for open immersions
(`ProEtale.CondensedRing.homCommutesWithFilteredColimits_openImmersionLowerShriek`) and under
`Ri_*` for closed immersions
(`homCommutesWithFilteredColimits_rightDerivedLowerStar_of_isClosedImmersion`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

end AlgebraicGeometry.ProEtale.CondensedRing
