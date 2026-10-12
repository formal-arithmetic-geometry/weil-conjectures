/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group V2
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Geometry.RingedSpace.Basic
import Sheaf.CategoryTheory.LocalizedModuleAdjunctionExact

/-! # Canonical adjunction maps in the geometric open-cover triangle

Source: Stacks Project, Tags 08BU, 08BT and 08BW.
(blueprint: lem-sc-open-cover-adjunction-triangle).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated

noncomputable section

namespace SheafOfModules

/-- The canonical comparison between nested derived restrictions.
Source: Stacks Project, Tag 08BW
(blueprint: lem-sc-open-cover-adjunction-triangle). -/
def openRestrictionComparison {S : Type u} [TopologicalSpace S]
    (R : Sheaf (Opens.grothendieckTopology S) RingCat.{u})
    {W U : Opens S} (i : W ⟶ U)
    [(overFunctor.{u} R U).Additive]
    [PreservesFiniteLimits (overFunctor.{u} R U)]
    [PreservesFiniteColimits (overFunctor.{u} R U)]
    [(overFunctor.{u} R W).Additive]
    [PreservesFiniteLimits (overFunctor.{u} R W)]
    [PreservesFiniteColimits (overFunctor.{u} R W)]
    [(overMap.{u} R i).Additive]
    [PreservesFiniteLimits (overMap.{u} R i)]
    [PreservesFiniteColimits (overMap.{u} R i)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} R)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (R.over U))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (R.over W))]
    : (overFunctor.{u} R U).mapDerivedCategory ⋙
      (overMap.{u} R i).mapDerivedCategory ≅ (overFunctor.{u} R W).mapDerivedCategory :=
  let A := overFunctor.{u} R U
  let B := overMap.{u} R i
  letI : PreservesFiniteLimits (A ⋙ B) := comp_preservesFiniteLimits A B
  letI : PreservesFiniteColimits (A ⋙ B) := comp_preservesFiniteColimits A B
  (Functor.mapDerivedCategoryCompIso A B).symm ≪≫
    Functor.mapDerivedCategoryNatIso (overFunctorMap.{u} R i)

/-- The geometric Mayer–Vietoris triangle with its arrows defined as adjunction mates.
No Hom identifications or shifted Hom groups are part of this statement.

Source: Stacks Project, Tags 08BU (lower-shriek triangle), 08BT (derived adjunction),
and 08BW (nested-open identifications).
(blueprint: lem-sc-open-cover-adjunction-triangle).

Proof: Represent E by a cochain complex K. For W = U ∩ V the exact extension by zero
functors give the termwise short exact sequence
0 → j_W! K|W → j_U! K|U ⊕ j_V! K|V → K → 0. Its maps are the canonical nested
extension map and its negative, and the two counits. Check exactness on stalks:
on W the maps are m ↦ (m,-m), (m,n) ↦ m+n; on only one open they are the identity
on the sole nonzero summand. The cover ensures there is no remaining stalk.
The short-exact-complex construction produces a distinguished triangle. Transport
it along Q K ≅ E and the exact-functor localization comparison isomorphisms.
For a nested inclusion W → U, transpose the canonical extension map under the W
adjunction. Its sectionwise construction gives the unit of the U adjunction
restricted to W, conjugated by the canonical nested restriction comparison.
The same identity holds termwise on K and descends through localization. Thus its
transpose is precisely c_U(E)⁻¹ ≫ R_WU(η_U(R_U E)) ≫ c_U(L_U R_U E), as displayed.
The V component has the negative sign. The second arrow is the pair of counits.
Any other chosen left adjoints and adjunctions are transported from these canonical
ones by the unique isomorphisms compatible with their right adjoints; mates and
counits commute with these isomorphisms. Distinguished triangles are invariant
under that transport. The formulas also apply when an open is empty or when U=V.
-/
theorem open_cover_adjunction_triangle (X : AlgebraicGeometry.RingedSpace.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (hR : R = (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)
    (U V : Opens X) (hcover : U ⊔ V = ⊤)
    [(overFunctor.{u} R U).Additive]
    [PreservesFiniteLimits (overFunctor.{u} R U)]
    [PreservesFiniteColimits (overFunctor.{u} R U)]
    [(overFunctor.{u} R V).Additive]
    [PreservesFiniteLimits (overFunctor.{u} R V)]
    [PreservesFiniteColimits (overFunctor.{u} R V)]
    [(overFunctor.{u} R (U ⊓ V)).Additive]
    [PreservesFiniteLimits (overFunctor.{u} R (U ⊓ V))]
    [PreservesFiniteColimits (overFunctor.{u} R (U ⊓ V))]
    [(overMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U)).Additive]
    [PreservesFiniteLimits (overMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U))]
    [PreservesFiniteColimits (overMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U))]
    [(overMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V)).Additive]
    [PreservesFiniteLimits (overMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V))]
    [PreservesFiniteColimits (overMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} R)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (R.over U))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (R.over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (R.over (U ⊓ V)))]
    (E : DerivedCategory (SheafOfModules.{u} R))
    (LU : DerivedCategory (SheafOfModules.{u} (R.over U)) ⥤
      DerivedCategory (SheafOfModules.{u} R))
    (LV : DerivedCategory (SheafOfModules.{u} (R.over V)) ⥤
      DerivedCategory (SheafOfModules.{u} R))
    (LW : DerivedCategory (SheafOfModules.{u} (R.over (U ⊓ V))) ⥤
      DerivedCategory (SheafOfModules.{u} R))
    (adjU : LU ⊣ (overFunctor.{u} R U).mapDerivedCategory)
    (adjV : LV ⊣ (overFunctor.{u} R V).mapDerivedCategory)
    (adjW : LW ⊣ (overFunctor.{u} R (U ⊓ V)).mapDerivedCategory) :
    let RU := (overFunctor.{u} R U).mapDerivedCategory
    let RV := (overFunctor.{u} R V).mapDerivedCategory
    let RW := (overFunctor.{u} R (U ⊓ V)).mapDerivedCategory
    let TU := (overMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U)).mapDerivedCategory
    let TV := (overMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V)).mapDerivedCategory
    let cU := openRestrictionComparison R (homOfLE inf_le_left : U ⊓ V ⟶ U)
    let cV := openRestrictionComparison R (homOfLE inf_le_right : U ⊓ V ⟶ V)
    let κU := (adjW.homEquiv (RW.obj E) (LU.obj (RU.obj E))).symm
      (cU.inv.app E ≫ TU.map (adjU.unit.app (RU.obj E)) ≫ cU.hom.app (LU.obj (RU.obj E)))
    let κV := (adjW.homEquiv (RW.obj E) (LV.obj (RV.obj E))).symm
      (cV.inv.app E ≫ TV.map (adjV.unit.app (RV.obj E)) ≫ cV.hom.app (LV.obj (RV.obj E)))
    ∃ δ : E ⟶ (LW.obj (RW.obj E))⟦(1 : ℤ)⟧,
      Triangle.mk (biprod.lift κU (-κV))
        (biprod.desc (adjU.counit.app E) (adjV.counit.app E)) δ ∈ distTriang _ := by
  sorry

end SheafOfModules
