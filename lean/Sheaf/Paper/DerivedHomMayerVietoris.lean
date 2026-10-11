/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Exact.Basic
import Mathlib.Geometry.RingedSpace.Basic

/-! # Mayer--Vietoris sequence for derived Hom

Source: Stacks Project, Cohomology, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris).

## Main statements

- `derived_hom_mayer_vietoris`: exactness at global and local derived Hom.
- `derivedOpenHomRestriction`: the canonical restriction to a smaller open.
-/

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry

/-- The structure sheaf viewed as a sheaf of rings, as in the module-stalk siblings.
Source: Stacks, Tag 08BW (blueprint: lem-sc-derived-hom-mayer-vietoris). -/
private abbrev moduleRings (X : RingedSpace.{u}) :=
  (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf

/-- Restriction to an open is additive. Source: Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris).
Proof: restriction precomposes the sectionwise linear maps with the forgetful functor
from the localized site; sums of maps are computed sectionwise. -/
theorem moduleOverFunctor_additive_proof (X : RingedSpace.{u}) (U : Opens X) :
    (SheafOfModules.overFunctor.{u} (moduleRings X) U).Additive :=
  sorry

/-- Additivity of open restriction; Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris). -/
instance moduleOverFunctor_additive (X : RingedSpace.{u}) (U : Opens X) :
    (SheafOfModules.overFunctor.{u} (moduleRings X) U).Additive :=
  moduleOverFunctor_additive_proof X U

/-- Restriction to an open preserves finite limits. Source: Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris).
Proof: kernels and finite products of module sheaves are computed sectionwise, and
restriction retains precisely the sections on opens contained in the chosen open. -/
theorem moduleOverFunctor_limits_proof (X : RingedSpace.{u}) (U : Opens X) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (moduleRings X) U) :=
  sorry

/-- Finite-limit preservation of open restriction; Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris). -/
instance moduleOverFunctor_limits (X : RingedSpace.{u}) (U : Opens X) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{u} (moduleRings X) U) :=
  moduleOverFunctor_limits_proof X U

/-- Restriction to an open preserves finite colimits. Source: Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris).
Proof: finite sums are sectionwise. Cokernels are sheafified sectionwise cokernels;
sheafification commutes with open restriction since covering families of an open
contained in the chosen open are the same in the localized site. -/
theorem moduleOverFunctor_colimits_proof (X : RingedSpace.{u}) (U : Opens X) :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (moduleRings X) U) :=
  sorry

/-- Finite-colimit preservation of open restriction; Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris). -/
instance moduleOverFunctor_colimits (X : RingedSpace.{u}) (U : Opens X) :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{u} (moduleRings X) U) :=
  moduleOverFunctor_colimits_proof X U

/-- Restriction between two opens is additive. Source: Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris).
Proof: `overMap` restricts sectionwise linear maps, and therefore preserves their sums. -/
theorem moduleOverMap_additive_proof (X : RingedSpace.{u}) {W U : Opens X} (i : W ⟶ U) :
    (SheafOfModules.overMap.{u} (moduleRings X) i).Additive :=
  sorry

/-- Additivity of restriction between opens; Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris). -/
instance moduleOverMap_additive (X : RingedSpace.{u}) {W U : Opens X} (i : W ⟶ U) :
    (SheafOfModules.overMap.{u} (moduleRings X) i).Additive :=
  moduleOverMap_additive_proof X i

/-- Restriction between opens preserves finite limits. Source: Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris).
Proof: the sectionwise descriptions of kernels and finite products are unchanged
when the localized site is further restricted to the smaller open. -/
theorem moduleOverMap_limits_proof (X : RingedSpace.{u}) {W U : Opens X} (i : W ⟶ U) :
    PreservesFiniteLimits (SheafOfModules.overMap.{u} (moduleRings X) i) :=
  sorry

/-- Finite-limit preservation between opens; Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris). -/
instance moduleOverMap_limits (X : RingedSpace.{u}) {W U : Opens X} (i : W ⟶ U) :
    PreservesFiniteLimits (SheafOfModules.overMap.{u} (moduleRings X) i) :=
  moduleOverMap_limits_proof X i

/-- Restriction between opens preserves finite colimits. Source: Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris).
Proof: sums are sectionwise and cokernels are sheafified sectionwise cokernels.
Coverings on each smaller open agree in the two localized sites, so sheafification
and restriction commute. -/
theorem moduleOverMap_colimits_proof (X : RingedSpace.{u}) {W U : Opens X} (i : W ⟶ U) :
    PreservesFiniteColimits (SheafOfModules.overMap.{u} (moduleRings X) i) :=
  sorry

/-- Finite-colimit preservation between opens; Stacks, Tag 08BW
(blueprint: lem-sc-derived-hom-mayer-vietoris). -/
instance moduleOverMap_colimits (X : RingedSpace.{u}) {W U : Opens X} (i : W ⟶ U) :
    PreservesFiniteColimits (SheafOfModules.overMap.{u} (moduleRings X) i) :=
  moduleOverMap_colimits_proof X i

/-- Restrict a morphism on `U` to `W`, transporting along the canonical restriction iso.
Source: Stacks, Tag 08BW (blueprint: lem-sc-derived-hom-mayer-vietoris). -/
def derivedOpenHomRestriction (X : RingedSpace.{u}) {W U : Opens X} (i : W ⟶ U)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X).over U))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X).over W))]
    {E F : DerivedCategory (SheafOfModules.{u} (moduleRings X))}
    (f : (SheafOfModules.overFunctor.{u} (moduleRings X) U).mapDerivedCategory.obj E ⟶
      (SheafOfModules.overFunctor.{u} (moduleRings X) U).mapDerivedCategory.obj F) :
    (SheafOfModules.overFunctor.{u} (moduleRings X) W).mapDerivedCategory.obj E ⟶
      (SheafOfModules.overFunctor.{u} (moduleRings X) W).mapDerivedCategory.obj F :=
  let A := SheafOfModules.overFunctor.{u} (moduleRings X) U
  let B := SheafOfModules.overMap.{u} (moduleRings X) i
  letI : PreservesFiniteLimits (A ⋙ B) := comp_preservesFiniteLimits A B
  letI : PreservesFiniteColimits (A ⋙ B) := comp_preservesFiniteColimits A B
  let e := (Functor.mapDerivedCategoryCompIso A B).symm ≪≫
    Functor.mapDerivedCategoryNatIso (SheafOfModules.overFunctorMap.{u} (moduleRings X) i)
  e.inv.app E ≫ (SheafOfModules.overMap.{u} (moduleRings X) i).mapDerivedCategory.map f ≫
    e.hom.app F

/-- Mayer--Vietoris exactness at global Hom and at the pair of local Hom groups.
Source: Stacks, Tag 08BW (blueprint: lem-sc-derived-hom-mayer-vietoris).

Proof: apply the distinguished Mayer--Vietoris triangle
(`lem-sc-derived-mayer-vietoris-triangle`) to `E`. Contravariant Hom into `F`
gives the long exact sequence (`lem-weil-pbc-hom-out-of-triangle-exact`).
The derived extension-by-zero/restriction adjunction
(`lem-sc-derived-open-shriek-derived-adjunction`) identifies its terms with
Hom on the three opens and global Hom. The preceding term is negative Ext on
the overlap. The first arrow is the pair of restrictions; the next is their
difference, because the triangle's first arrow is the difference of the two
extension-by-zero maps. Thus the sequence is exact at both specified terms. -/
theorem derived_hom_mayer_vietoris
    (X : RingedSpace.{u}) (U V : Opens X) (hcover : U ⊔ V = ⊤)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X).over U))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X).over (U ⊓ V)))]
    (E F : DerivedCategory (SheafOfModules.{u} (moduleRings X))) :
    let R_U := (SheafOfModules.overFunctor.{u} (moduleRings X) U).mapDerivedCategory
    let R_V := (SheafOfModules.overFunctor.{u} (moduleRings X) V).mapDerivedCategory
    let R_UV := (SheafOfModules.overFunctor.{u} (moduleRings X) (U ⊓ V)).mapDerivedCategory
    ∃ (negExt : (R_UV.obj E ⟶ (R_UV.obj F)⟦(-1 : ℤ)⟧) →+ (E ⟶ F)),
      Function.Exact negExt (fun f => (R_U.map f, R_V.map f)) ∧
      Function.Exact
        (fun f : E ⟶ F => (R_U.map f, R_V.map f))
        (fun p : (R_U.obj E ⟶ R_U.obj F) × (R_V.obj E ⟶ R_V.obj F) =>
          derivedOpenHomRestriction X (homOfLE inf_le_left) p.1 -
            derivedOpenHomRestriction X (homOfLE inf_le_right) p.2) :=
  sorry

end AlgebraicGeometry
