/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.RingedTopoiTensorComparisonData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Limits.Types.Products

/-!
# Canonical tensor pullback with independent site universes

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0G7E;
Modules on Sites, Tag 03EL
(blueprint: lem-weil-pbc-ringed-topoi-derived-tensor-pullback).

This is the general canonical representative interface, with a site-object universe s and an
independent site-morphism universe h. Rings and modules live in max s h, as in the
published K-flat interface. Both sites retain their actual Hom universe. The ring map is arbitrary,
  including coefficient quotients, and
the geometric morphism can be the etale-to-pro-etale comparison. The pure-tensor,
unit and signed total-complex normalizations are retained verbatim. Public imports
retain both earlier interfaces for existing callers.
-/

@[expose] public section

set_option Elab.async false

set_option autoImplicit false

universe s h w u uC vC uD vD

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace SheafOfModules.CanonicalTensorPullbackOfUniverses

-- Both site sizes fit the coefficient universe.
attribute [local instance 20000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize

set_option backward.isDefEq.respectTransparency true

variable {C D : Type s} [Category.{h} C] [Category.{h} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  (R : Sheaf JC CommRingCat.{max s h}) (S RI : Sheaf JD CommRingCat.{max s h})
  (uInv : Sheaf JC (Type (max s h)) ⥤ Sheaf JD (Type (max s h)))
  (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
  (L : SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
    RingCat.{max s h})).obj R) ⥤
      SheafOfModules.{max s h} ((sheafCompose JD (forget₂ CommRingCat.{max s h}
        RingCat.{max s h})).obj S))
  (hobj : ∀ M : SheafOfModules.{max s h} ((sheafCompose JC (forget₂ CommRingCat.{max s h}
    RingCat.{max s h})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))

open scoped ChangeOfRings

attribute [local irreducible] monoidalCategory
attribute [local irreducible] PresheafOfModules.sheafificationAdjunction
attribute [local irreducible] PresheafOfModules.sheafification

section TensorSections

attribute [local instance 30000] weakSheafification additiveCompose ringCompose

attribute [local irreducible] CochainTensorComparison.scalarInsertion

open scoped ChangeOfRings TensorProduct
set_option synthInstance.maxSize 2048

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {D : Type uD} [Category.{vD} D] [EssentiallySmall.{u} D]
  {J : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (A B : Sheaf J CommRingCat.{u})
set_option hygiene false in
local notation "𝓡" R => (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

@[no_expose] private noncomputable def ts (M N : SheafOfModules.{u} (𝓡 B))
    (W : Dᵒᵖ) (m : M.val.obj W) (n : N.val.obj W) :
    ((monoidalCategory B).tensorObj M N).val.obj W :=
  ringedComparisonPure B M N W m n
@[no_expose] private noncomputable def tensorPair (M N : SheafOfModules.{u} (𝓡 B))
    (Z : Sheaf J (Type u))
    (x : Z ⟶ ((toSheaf (𝓡 B) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj M))
    (y : Z ⟶ ((toSheaf (𝓡 B) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj N)) :
    Z ⟶ ((toSheaf (𝓡 B) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})).obj
      ((monoidalCategory B).tensorObj M N)) :=
  ⟨{ app := fun W ↦ ↾fun t ↦ ts B M N W (x.hom.app W t) (y.hom.app W t)
     naturality := by
       intro W V i
       ext t
       have hx := NatTrans.naturality_apply x.hom i t
       have hy := NatTrans.naturality_apply y.hom i t
       change ts B M N V (x.hom.app V (Z.obj.map i t))
           (y.hom.app V (Z.obj.map i t)) =
         ((monoidalCategory B).tensorObj M N).val.map i
           (ts B M N W (x.hom.app W t) (y.hom.app W t))
       rw [hx, hy]
       exact (ts_naturality B M N i _ _).symm }⟩

variable (c : A ⟶ B)

@[no_expose] private noncomputable def ins (M : SheafOfModules.{u} (𝓡 A))
    (W : Dᵒᵖ) (m : M.val.obj W) : (changeOfRings.{vD, uD, u} c M).val.obj W :=
  CochainScalarConstruction.ins c M W m

end TensorSections

section TensorUniqueness

attribute [local instance 30000] weakSheafification additiveCompose ringCompose

set_option backward.isDefEq.respectTransparency true

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  [JC.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [JD.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
  (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
  (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
  (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
  (hobj : ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))

set_option backward.isDefEq.respectTransparency.types true

-- Normalize the record projection while its generalized elements are abstract.

-- The two data fields determine the record; its remaining fields are propositions.

end TensorUniqueness

namespace UnitConstruction

attribute [local instance 30000] weakSheafification additiveCompose ringCompose

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (R : Sheaf J CommRingCat.{u}) (A : Sheaf K CommRingCat.{u})
  (F : Sheaf J (Type u) ⥤ Sheaf K (Type u)) (I : AlgebraicInverseImage F R A)

open MonoidalCategory

attribute [local semireducible] monoidalCategory
attribute [local instance 2000] cochainModulesMonoidal

-- Keep the concrete coefficient unit in the API without expanding the localization.

-- Specialize tensor-unit cancellation once, with concrete units in the signature.

end UnitConstruction

attribute [local irreducible] ringedComparisonPure tensorObjIsoSheafification

attribute [local irreducible] UnitConstruction.unitIso UnitConstruction.scalarUnitIso
  UnitConstruction.pullbackUnitIso

section GenericUnit

attribute [local instance 30000] weakSheafification additiveCompose ringCompose

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}
  [JC.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [JD.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (R : Sheaf JC CommRingCat.{u}) (S RI : Sheaf JD CommRingCat.{u})
  (uInv : Sheaf JC (Type u) ⥤ Sheaf JD (Type u))
  (I : AlgebraicInverseImage uInv R RI) (c : RI ⟶ S)
  (L : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose JD (forget₂ CommRingCat.{u} RingCat.{u})).obj S))
  (hobj : ∀ M : SheafOfModules.{u} ((sheafCompose JC (forget₂ CommRingCat.{u} RingCat.{u})).obj R),
      L.obj M = changeOfRings c (I.modules.obj M))

-- The explicit-unit API keeps the localized monoidal structure abstract.

attribute [local semireducible] monoidalCategory
attribute [local semireducible] UnitConstruction.explicitRightUnitor

end GenericUnit

attribute [local semireducible] monoidalCategory
attribute [local semireducible] UnitConstruction.explicitRightUnitor

attribute [local irreducible] monoidalCategory
attribute [local instance 20000] cochainTensorLeftPreservesColimits
  cochainTensorRightPreservesColimits

attribute [local irreducible] CanonicalRingedTensorComparison.total

end SheafOfModules.CanonicalTensorPullbackOfUniverses
