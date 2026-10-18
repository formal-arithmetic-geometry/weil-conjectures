/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.OpenCoverAdjunctionTriangle
public import Mathlib.SetTheory.Ordinal.Basic
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.Algebra.Homology.OpenRestrictionAdjunctionExact
import Sheaf.Algebra.Homology.KInjectiveRestrictOpen
import WeilConjectures.AlgebraicGeometry.Modules.ExtensionByZeroAdjunction
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.ModuleStalkFilteredColimit
import WeilConjectures.Algebra.Homology.ModuleStalkExact
import Sheaf.AlgebraicGeometry.DerivedBasisLocalHomGlue
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Topology.Sheaves.Stalks

/-! # Derived gluing on a continuous ordinal open cover

Source: Stacks Project, Cohomology, Tag 0D6B (lemma-glueing-increasing-union),
specialized to schemes (blueprint: lem-trf-derived-basis-increasing-union).

Local module categories use the localized open site, identified with modules on
`U.toScheme` by `Scheme.Modules.overEquiv U`. All restriction functors are the
shared `SheafOfModules.overFunctor` and `SheafOfModules.overMap`.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

/-- The sectionwise identity comparing successive restrictions between three opens.
Source: Stacks Project, Cohomology, Tag 0D6B, the cocycle convention
(blueprint: lem-trf-derived-basis-increasing-union). -/
def moduleOpenMapCompIso (X : Scheme.{u}) {T V U : X.Opens}
    (i : T ⟶ V) (j : V ⟶ U) :
    SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) j ⋙
      SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i ≅
    SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (i ≫ j) :=
  NatIso.ofComponents fun M ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso <|
      PresheafOfModules.isoMk (fun _ ↦ Iso.refl _)

/-- The canonical derived comparison from successive to direct open restriction.
Source: Stacks Project, Cohomology, Tag 0D6B, the cocycle convention
(blueprint: lem-trf-derived-basis-increasing-union). -/
def derivedModuleOpenMapCompIso (X : Scheme.{u}) {T V U : X.Opens}
    (i : T ⟶ V) (j : V ⟶ U)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over T))] :
    (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) j).mapDerivedCategory ⋙
      (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i).mapDerivedCategory ≅
    (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) (i ≫ j)).mapDerivedCategory :=
  letI : PreservesFiniteLimits
      (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) j ⋙
        SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i) :=
    comp_preservesFiniteLimits _ _
  letI : PreservesFiniteColimits
      (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) j ⋙
        SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i) :=
    comp_preservesFiniteColimits _ _
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (moduleOpenMapCompIso X i j)

/-- Compatible derived objects with no negative self extensions glue along a continuous
ordinal open cover.
Source: Stacks Project, Cohomology, Tag 0D6B (lemma-glueing-increasing-union)
(blueprint: lem-trf-derived-basis-increasing-union).

Proof:
1. For an empty ordinal the covering scheme is empty, so use the zero complex.
   Otherwise choose K-injective representatives I_alpha using
   `prop-pur-kinjective-resolutions-exist`. Open restriction is exact and preserves
   K-injectives (`lem-sc-derived-open-restriction-adjunction-exact`,
   `lem-sc-derived-k-injective-restrict-open`); the exact-functor derived comparison
   identifies their restrictions (`lem-sf-exact-functor-derived-triangulated`).
2. Use the normalized extension-by-zero adjunction of
   `lem-weil-pbc-module-extension-by-zero-adjunction`. Its interior unit is an
   isomorphism by `lem-weil-pbc-sets-sheaf-iso-on-stalks`. Adjoint chain maps induce
   extension-by-zero transition maps; naturality turns strict composition of the
   chain maps into strict composition of these transitions.
3. Construct chain maps I_beta to I_alpha restricted to W_beta by ordinal recursion,
   representing the inverse transition isomorphisms. At a successor choose the map
   from the predecessor by `lem-weil-pbc-kinjective-hom-derived`, then compose it
   with all earlier maps. The cocycle implies the correct derived classes.
4. At a nonzero limit form the termwise colimit C_alpha of the extensions of earlier
   I_beta by `lem-weil-pbc-module-sheaves-colimits-forgetful`. Its differential
   squares to zero on every coprojection. The restricted coprojections s_beta
   satisfy strict compatibility with the earlier chain maps.
5. At x in W_beta, `lem-weil-pbc-module-stalk-filtered-colimit` computes this stalk
   colimit on the cofinal tail beta <= gamma < alpha. The normalized extension
   stalk formula identifies its terms with (I_gamma)_x and its transitions with
   the chosen maps, which are quasi-isomorphisms by
   `lem-weil-pbc-module-stalk-exact`.
6. Exact filtered colimits (`lem-weil-pbc-filtered-colimit-abelian-groups-exact`)
   commute with cycles and boundaries. Thus cohomology of the stalk colimit is
   the colimit of the cohomologies. All transitions are isomorphisms, so each
   s_beta is a stalkwise quasi-isomorphism, hence a quasi-isomorphism by
   `lem-weil-pbc-module-stalk-exact`.
7. On the earlier opens, compare C_alpha with K_alpha using the inverse s_beta and
   the prescribed r_beta^alpha. Strict compatibility and the cocycle make these
   maps agree. Continuity gives a cover with intersections the smaller member;
   the negative cross Hom groups vanish since both objects are locally K_beta.
   Apply `lem-trf-derived-basis-local-hom-glue` to these maps and their inverses.
   Its uniqueness clause shows the resulting global maps are inverse.
8. Represent C_alpha to K_alpha (in this direction) by a chain map to I_alpha via
   `lem-weil-pbc-kinjective-hom-derived`. Composing with the coprojections closes
   the strict recursion. This uses Hom gluing, not the desired effectivity theorem.
9. On X take the final termwise colimit of the extensions of all I_alpha. The
   same filtered-tail stalk calculation from steps 5--6 makes every restricted
   coprojection a quasi-isomorphism, also for a successor final ordinal.
10. Its derived object is K. Invert the restricted coprojections to obtain r_alpha;
    the strict chain-map equations and their prescribed derived classes give the
    required compatibility. Empty and repeated opens satisfy the same formulas.
-/
theorem derived_basis_increasing_union
    (X : Scheme.{u}) (lambda : Ordinal.{v})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (W : lambda.ToType → X.Opens) (hincreasing : Monotone W)
    (hcover : iSup W = ⊤)
    (hcontinuous : ∀ alpha : lambda.ToType, Order.IsSuccPrelimit alpha →
      W alpha = ⨆ beta : {beta : lambda.ToType // beta < alpha}, W beta.val)
    (K : ∀ alpha : lambda.ToType,
      DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (W alpha))))
    (hnegative : ∀ (alpha : lambda.ToType) (i : ℤ), i < 0 →
      Subsingleton (K alpha ⟶ (K alpha)⟦i⟧))
    (r : ∀ (beta alpha : lambda.ToType) (h : beta < alpha),
      (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
        (homOfLE (hincreasing h.le))).mapDerivedCategory.obj (K alpha) ≅ K beta)
    (hcocycle : ∀ (gamma beta alpha : lambda.ToType)
        (hgb : gamma < beta) (hba : beta < alpha),
      (derivedModuleOpenMapCompIso X
        (homOfLE (hincreasing hgb.le)) (homOfLE (hincreasing hba.le))).inv.app (K alpha) ≫
        (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
          (homOfLE (hincreasing hgb.le))).mapDerivedCategory.map (r beta alpha hba).hom ≫
        (r gamma beta hgb).hom = (r gamma alpha (hgb.trans hba)).hom) :
    ∃ (L : schemeDerivedCategory X)
      (rho : ∀ alpha : lambda.ToType,
        (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
          (W alpha)).mapDerivedCategory.obj L ≅ K alpha),
      ∀ (beta alpha : lambda.ToType) (h : beta < alpha),
        (SheafOfModules.openRestrictionComparison (moduleRings X.toRingedSpace)
          (homOfLE (hincreasing h.le))).inv.app L ≫
          (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace)
            (homOfLE (hincreasing h.le))).mapDerivedCategory.map (rho alpha).hom ≫
          (r beta alpha h).hom = (rho beta).hom := by
  sorry

end AlgebraicGeometry
