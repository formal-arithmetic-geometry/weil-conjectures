/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N6
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Sheaf.AlgebraicGeometry.DerivedBasisIncreasingUnion
import Sheaf.AlgebraicGeometry.DerivedBasisLocalHomGlue

/-! # Extension of basis identifications at a continuous ordinal limit

Source: Stacks Project, Cohomology, Tags 0D6B and 0D6C, limit step and final paragraph
(blueprint: lem-trf-derived-basis-limit-extension).

Modules on an open use the localized open site, as in the increasing-union lemma.
This is canonically equivalent to modules on the open subscheme. All comparisons
below are the canonical comparisons of successive derived restrictions.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- Restrict a map from a restricted object, using the canonical composition comparison.
Source: Stacks Project, Cohomology, Tags 0D6B and 0D6C, restriction conventions
(blueprint: lem-trf-derived-basis-limit-extension). -/
noncomputable def derivedOpenMapRestrictHom (X : Scheme.{u}) {O U V : X.Opens}
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over O))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    (i : V ⟶ U) (j : U ⟶ O)
    {F : DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over O))}
    {K : DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))}
    (a : (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) j).mapDerivedCategory.obj
      F ⟶ K) :
    (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (i ≫ j)).mapDerivedCategory.obj
      F ⟶
    (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i).mapDerivedCategory.obj K :=
  (derivedModuleOpenMapCompIso X i j).inv.app F ≫
    (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i).mapDerivedCategory.map a

/-- Extend every basis identification at a continuous ordinal limit, including basis opens
not contained in any one stage.
Source: Stacks Project, Cohomology, Tags 0D6B and 0D6C
(blueprint: lem-trf-derived-basis-limit-extension).

Proof:
1. Apply `lem-trf-derived-basis-increasing-union` on the limit union, with objects
   F_beta. Continuity, negative self Hom vanishing and the cocycle give F and r_beta.
2. For a basis member U in the union, let C_U consist of the basis members V inside
   U and some W_beta. This covers U: choose a stage, a basis member in that stage,
   then refine its intersection with U. It refines intersections by the same rule.
   On V define a_V by r_beta, s_beta,V and the inverse of rho_V^U. The r cocycle
   and compatibility with s show independence of beta. The rho cocycle and the
   solution equations show compatibility under inclusions.
3. Both objects on V are isomorphic to K_V. Conjugating with those isomorphisms
   gives negative Hom vanishing for both cross pairs and both self pairs. Apply
   `lem-trf-derived-basis-local-hom-glue` to a_V and its inverses. The resulting
   global maps are inverse by Hom injectivity. This gives s_U and its uniqueness
   among all morphisms with the specified restrictions.
4. For T inside U compare rho_T^U composed with s_U restricted to T against s_T.
   On every V in C_T the rho cocycle identifies their formulas. Hom injectivity
   in `lem-trf-derived-basis-local-hom-glue` proves equality. Thus all s_U form a
   solution, even when U crosses every stage.
5. If U is inside W_beta, use V=U in its defining equation and rho_U^U=1 to get
   the stage equation. The r equations came from step 1. Empty opens and empty
   unions are covered by the empty-case Hom bijections of the same gluing lemma.
   No finite subcover, quasi-compactness or boundedness is used. -/
theorem derived_basis_limit_extension
    (X : Scheme.{u}) (lambda : Ordinal.{v}) (hlimit : Order.IsSuccLimit lambda)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (B : Set X.Opens) (hcover : sSup B = ⊤)
    (hrefine : ∀ U ∈ B, ∀ V ∈ B,
      sSup {T : X.Opens | T ∈ B ∧ T ≤ U ⊓ V} = U ⊓ V)
    (K : ∀ U : {U : X.Opens // U ∈ B},
      DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U.val)))
    (rho : ∀ (U V : {U : X.Opens // U ∈ B}) (h : V.val ≤ U.val),
      (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE h)).mapDerivedCategory.obj (K U) ≅ K V)
    (rho_id : ∀ U : {U : X.Opens // U ∈ B},
      (rho U U le_rfl).hom =
        (Functor.mapDerivedCategoryNatIso
          (NatIso.ofComponents (fun M ↦
            (SheafOfModules.fullyFaithfulForget _).preimageIso
              (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _))) :
            SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
              (homOfLE (le_refl U.val)) ≅
            𝟭 (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U.val))) ≪≫
          Functor.mapDerivedCategoryIdIso _).hom.app (K U))
    (rho_comp : ∀ (U V T : {U : X.Opens // U ∈ B})
        (hVU : V.val ≤ U.val) (hTV : T.val ≤ V.val),
      derivedOpenMapRestrictHom X (homOfLE hTV) (homOfLE hVU) (rho U V hVU).hom ≫
        (rho V T hTV).hom = (rho U T (hTV.trans hVU)).hom)
    (hnegative : ∀ (U : {U : X.Opens // U ∈ B}) (i : ℤ), i < 0 →
      Subsingleton (K U ⟶ (K U)⟦i⟧))
    (W : lambda.ToType → X.Opens) (hincreasing : Monotone W)
    (hunion : ∀ beta : lambda.ToType, sSup {U : X.Opens | U ∈ B ∧ U ≤ W beta} = W beta)
    (hcontinuous : ∀ delta : lambda.ToType, Order.IsSuccPrelimit delta →
      W delta = ⨆ beta : {beta : lambda.ToType // beta < delta}, W beta.val)
    (F : ∀ beta : lambda.ToType,
      DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (W beta))))
    (s : ∀ (beta : lambda.ToType) (U : {U : X.Opens // U ∈ B}) (h : U.val ≤ W beta),
      (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE h)).mapDerivedCategory.obj (F beta) ≅ K U)
    (hs : ∀ (beta : lambda.ToType) (U V : {U : X.Opens // U ∈ B})
        (hU : U.val ≤ W beta) (hVU : V.val ≤ U.val),
      derivedOpenMapRestrictHom X (homOfLE hVU) (homOfLE hU) (s beta U hU).hom ≫
        (rho U V hVU).hom = (s beta V (hVU.trans hU)).hom)
    (hFnegative : ∀ (beta : lambda.ToType) (i : ℤ), i < 0 →
      Subsingleton (F beta ⟶ (F beta)⟦i⟧))
    (r : ∀ (gamma beta : lambda.ToType) (h : gamma < beta),
      (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (hincreasing h.le))).mapDerivedCategory.obj (F beta) ≅ F gamma)
    (hr : ∀ (eta gamma beta : lambda.ToType) (heg : eta < gamma) (hgb : gamma < beta),
      derivedOpenMapRestrictHom X (homOfLE (hincreasing heg.le))
          (homOfLE (hincreasing hgb.le)) (r gamma beta hgb).hom ≫
        (r eta gamma heg).hom = (r eta beta (heg.trans hgb)).hom)
    (hrs : ∀ (gamma beta : lambda.ToType) (hgb : gamma < beta)
        (U : {U : X.Opens // U ∈ B}) (hU : U.val ≤ W gamma),
      derivedOpenMapRestrictHom X (homOfLE hU) (homOfLE (hincreasing hgb.le))
          (r gamma beta hgb).hom ≫
        (s gamma U hU).hom = (s beta U (hU.trans (hincreasing hgb.le))).hom) :
    ∃ (L : DerivedCategory
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (iSup W))))
      (sL : ∀ (U : {U : X.Opens // U ∈ B}) (h : U.val ≤ iSup W),
        (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
          (homOfLE h)).mapDerivedCategory.obj L ≅ K U)
      (rL : ∀ beta : lambda.ToType,
        (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
          (homOfLE (le_iSup W beta))).mapDerivedCategory.obj L ≅ F beta),
      (∀ (U V : {U : X.Opens // U ∈ B}) (hU : U.val ≤ iSup W) (hVU : V.val ≤ U.val),
        derivedOpenMapRestrictHom X (homOfLE hVU) (homOfLE hU) (sL U hU).hom ≫
          (rho U V hVU).hom = (sL V (hVU.trans hU)).hom) ∧
      (∀ (gamma beta : lambda.ToType) (hgb : gamma < beta),
        derivedOpenMapRestrictHom X (homOfLE (hincreasing hgb.le))
            (homOfLE (le_iSup W beta)) (rL beta).hom ≫
          (r gamma beta hgb).hom = (rL gamma).hom) ∧
      (∀ (beta : lambda.ToType) (U : {U : X.Opens // U ∈ B}) (hU : U.val ≤ W beta),
        (sL U (hU.trans (le_iSup W beta))).hom =
          derivedOpenMapRestrictHom X (homOfLE hU) (homOfLE (le_iSup W beta))
              (rL beta).hom ≫
            (s beta U hU).hom) ∧
      (∀ (U : {U : X.Opens // U ∈ B}) (hU : U.val ≤ iSup W),
        (∀ (beta : lambda.ToType) (V : {U : X.Opens // U ∈ B})
            (hVU : V.val ≤ U.val) (hV : V.val ≤ W beta),
          derivedOpenMapRestrictHom X (homOfLE hVU) (homOfLE hU) (sL U hU).hom ≫
              (rho U V hVU).hom =
            derivedOpenMapRestrictHom X (homOfLE hV) (homOfLE (le_iSup W beta))
                (rL beta).hom ≫
              (s beta V hV).hom) ∧
        (∀ a : (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
            (homOfLE hU)).mapDerivedCategory.obj L ⟶ K U,
          (∀ (beta : lambda.ToType) (V : {U : X.Opens // U ∈ B})
              (hVU : V.val ≤ U.val) (hV : V.val ≤ W beta),
            derivedOpenMapRestrictHom X (homOfLE hVU) (homOfLE hU) a ≫
                (rho U V hVU).hom =
              derivedOpenMapRestrictHom X (homOfLE hV) (homOfLE (le_iSup W beta))
                  (rL beta).hom ≫
                (s beta V hV).hom) → a = (sL U hU).hom)) := by
  sorry

end AlgebraicGeometry
