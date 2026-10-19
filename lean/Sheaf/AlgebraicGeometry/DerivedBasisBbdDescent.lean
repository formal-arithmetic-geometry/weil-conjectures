/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q136
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.DerivedBasisIncreasingUnion
import Sheaf.AlgebraicGeometry.DerivedBasisLocalHomGlue
import Sheaf.AlgebraicGeometry.DerivedOpenGluing

/-! # BBD descent for derived objects with vanishing negative self extensions

Source: Stacks Project, Cohomology, Tags 0D67 and 0D6C
(blueprint: lem-trf-derived-basis-bbd-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- The sectionwise identity for restriction from an open to itself.
Source: Stacks Project, Cohomology, Situation 0D67, identity normalization
(blueprint: lem-trf-derived-basis-bbd-descent). -/
noncomputable def moduleOpenMapIdIso (X : Scheme.{u}) (U : X.Opens) :
    SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE (le_refl U)) ≅
      𝟭 (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
  NatIso.ofComponents fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso <|
      PresheafOfModules.isoMk (fun _ ↦ Iso.refl _)

/-- The canonical identity comparison for derived restriction to the same open.
Source: Stacks Project, Cohomology, Situation 0D67, identity normalization
(blueprint: lem-trf-derived-basis-bbd-descent). -/
noncomputable def derivedModuleOpenMapIdIso (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
      (homOfLE (le_refl U))).mapDerivedCategory ≅
        𝟭 (DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))) :=
  Functor.mapDerivedCategoryNatIso (moduleOpenMapIdIso X U) ≪≫
    Functor.mapDerivedCategoryIdIso _

set_option maxHeartbeats 2000000 in
-- The canonical identity comparison and uniqueness restriction map require extra elaboration.
/-- BBD descent for derived objects over an intersection-refining open cover.
Source: Stacks Project, Cohomology, Tags 0D67 and 0D6C
(blueprint: lem-trf-derived-basis-bbd-descent).

Proof:
1. On any union O of members of B, the members contained in O cover it and
   refine intersections. For two solutions, their cross negative Hom groups
   vanish locally, since both restrictions are isomorphic to K_U. Apply
   `lem-trf-derived-basis-local-hom-glue` to the compatible local comparisons
   and their inverses. Hom injectivity makes the resulting maps inverse and
   unique. The same lemma gives negative self Hom vanishing for every solution.
2. For solutions on O1 and O2, refine their intersection by members of B.
   The local comparisons from step 1 glue uniquely there. On triple overlaps
   they compose correctly because their local formulas cancel the middle map.
3. Well-order B and let W_alpha be the union of earlier members. Construct
   solutions by transfinite recursion. Step 1 gives unique comparisons between
   stages; uniqueness gives their cocycle. Start with the zero complex on the
   empty scheme, including when the empty open belongs to B.
4. At a successor glue the solution on W_alpha to K_Ualpha using the overlap
   isomorphism from step 2 and `lem-sc-derived-open-gluing`. Define the structure
   maps on members contained in either open. The overlap equation makes the
   two formulas agree and the original cocycle gives inclusion compatibility.
5. For any remaining U in B inside the successor union, cover U by members
   contained in either of those two opens. Compose their structure maps with
   inverse rho transitions to K_U. Use `lem-trf-derived-basis-local-hom-glue`
   on these maps and their inverses. Its injectivity gives compatibility for
   all inclusions and agreement with the previous stage; step 1 gives vanishing.
6. At a nonzero limit the earlier W_beta form a continuous increasing cover.
   The unique comparisons satisfy the cocycle and negative self Hom vanishes
   by step 1. Apply `lem-trf-derived-basis-increasing-union` to obtain the
   limit object with compatible identifications on every W_beta.
7. A member U of B in the limit union need not lie in one earlier stage.
   Cover it by members lying in some W_beta. Their structure maps are
   independent of beta, since comparisons between stages preserve them.
   Move two indices to their maximum to check inclusion compatibility.
   Glue the resulting comparisons to K_U and their inverses by
   `lem-trf-derived-basis-local-hom-glue`; cross negative Hom vanishes locally.
8. Check the limit structure equations on that covering family, using Hom
   injectivity. This also gives agreement with every earlier stage. Recursion
   ends when the union is X; step 1 proves unique compatible isomorphism.
   Only a well-order of the set B is needed, without quasi-compactness. -/
theorem derived_basis_bbd_descent
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (B : Set X.Opens) (hcover : sSup B = ⊤)
    (hrefine : ∀ U ∈ B, ∀ V ∈ B,
      sSup {W : X.Opens | W ∈ B ∧ W ≤ U ⊓ V} = U ⊓ V)
    (K : ∀ U : {U : X.Opens // U ∈ B},
      DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U.val)))
    (rho : ∀ (U V : {U : X.Opens // U ∈ B}) (h : V.val ≤ U.val),
      (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (homOfLE h)).mapDerivedCategory.obj
          (K U) ≅ K V)
    (rho_id : ∀ U : {U : X.Opens // U ∈ B},
      (rho U U le_rfl).hom =
        (derivedModuleOpenMapIdIso X U.val).hom.app (K U))
    (rho_comp : ∀ (U V W : {U : X.Opens // U ∈ B})
      (hUV : V.val ≤ U.val) (hVW : W.val ≤ V.val),
      (derivedModuleOpenMapCompIso X (homOfLE hVW) (homOfLE hUV)).inv.app (K U) ≫
          (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
          (homOfLE hVW)).mapDerivedCategory.map (rho U V hUV).hom ≫
        (rho V W hVW).hom =
        (rho U W (hVW.trans hUV)).hom)
    (hnegative : ∀ (U : {U : X.Opens // U ∈ B}) (i : ℤ), i < 0 →
      Subsingleton (K U ⟶ K U⟦i⟧)) :
    ∃ (KX : schemeDerivedCategory X)
      (rhoX : ∀ U : {U : X.Opens // U ∈ B},
        (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
          U.val).mapDerivedCategory.obj KX ≅
          K U),
      (∀ (U V : {U : X.Opens // U ∈ B}) (h : V.val ≤ U.val),
        (SheafOfModules.openRestrictionComparison (moduleRings X.toRingedSpace)
            (homOfLE h)).inv.app KX ≫
          (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
              (homOfLE h)).mapDerivedCategory.map (rhoX U).hom ≫
            (rho U V h).hom = (rhoX V).hom) ∧
      ∀ (KX' : schemeDerivedCategory X)
        (rhoX' : ∀ U : {U : X.Opens // U ∈ B},
          (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
            U.val).mapDerivedCategory.obj KX' ≅
            K U),
        (∀ (U V : {U : X.Opens // U ∈ B}) (h : V.val ≤ U.val),
          (SheafOfModules.openRestrictionComparison (moduleRings X.toRingedSpace)
              (homOfLE h)).inv.app KX' ≫
            (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
                (homOfLE h)).mapDerivedCategory.map (rhoX' U).hom ≫
              (rho U V h).hom = (rhoX' V).hom) →
        ∃! a : KX ≅ KX',
          ∀ U : {U : X.Opens // U ∈ B},
            (rhoX U).hom ≫ (rhoX' U).inv =
              (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
                U.val).mapDerivedCategory.map a.hom := by
  sorry

end AlgebraicGeometry
