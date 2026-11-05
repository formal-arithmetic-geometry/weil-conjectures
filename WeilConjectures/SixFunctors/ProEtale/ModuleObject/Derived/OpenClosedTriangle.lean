/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Triangulated.RecollementTriangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleClosedPushforward
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenClosedConservative
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarShift

/-!
# The open–closed triangle on the ambient derived categories of module objects

Let `Λ` be a commutative condensed ring, `j : U ⟶ X` a quasi-compact open immersion and
`i : Z ⟶ X` a closed immersion onto its complement. On the ambient derived category
`D(Mod_{Λ_X})`, for every complex `K`, the counit `j_! Lj^* K ⟶ K` of `Dj_! ⊣ Lj^*` and the unit
`K ⟶ Ri_* Li^* K` of `Li^* ⊣ Ri_*` extend to a distinguished triangle
(`ProEtale.CondensedRing.exists_distTriang_openClosed_derived`).

This follows from the joint conservativity of `Lj^*` and `Li^*`
(`ProEtale.CondensedRing.jointlyReflectIsomorphisms_leftDerivedUpperStar_of_isCompl`), the full
faithfulness of `Dj_!` and of `Ri_*`, and the vanishing of `Lj^* Ri_*` and of `Li^* Dj_!`. This
file only depends on the derived six operations on module objects, not on the localizing
subcategories, so that it can be used below them in the import hierarchy.
-/
@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
  {X U Z : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j] (i : Z ⟶ X)
  [IsClosedImmersion i] (hij : IsCompl (Set.range i.base) (Set.range j.base))

end AlgebraicGeometry.ProEtale.CondensedRing
