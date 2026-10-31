/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
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
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.ProperBaseChange.GeometricModuleConstruction
import all WeilConjectures.ProperBaseChange.GeometricModuleTransport
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod

/-! # Tensor comparison for the algebraic inverse image

Source: Stacks Project, Modules on Sites, Tags 03D1--03D3, 03D7 and 03EL.
(blueprint: lem-pur-independent-inverse-image-tensor-comparison).

Transport the right-adjoint module operations, restrict the set adjunction to
linear and bilinear maps, and apply the sheaf tensor universal property.
All five site and coefficient universe parameters remain independent.
-/

@[expose] public section

universe u uC vC uD vD uE vE
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace SheafOfModules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

namespace CochainGeometricConstruction

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
    [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

set_option backward.isDefEq.respectTransparency true
open GeometricConstruction

end CochainGeometricConstruction

set_option backward.isDefEq.respectTransparency false
end SheafOfModules

namespace SheafOfModules.CochainScalarConstruction
open scoped TensorProduct ChangeOfRings
attribute [local irreducible] monoidalCategory
attribute [local instance 2000] cochainModulesMonoidal
private abbrev ringSheaf {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) :=
  (sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R

private noncomputable abbrev underlying {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (R : Sheaf J CommRingCat.{u}) :=
  toSheaf (ringSheaf R) ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{u})

section Pure
variable {C : Type uC} [Category.{vC} C] [EssentiallySmall.{u} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (R : Sheaf J CommRingCat.{u})

/-- The image of a sectionwise pure tensor in the sheaf tensor.
Source: Stacks 03EK (blueprint: def-weil-pbc-ringed-tensor-section-calculus). -/
private noncomputable def pure (M N : SheafOfModules.{u} (ringSheaf R))
    (W : Cᵒᵖ) (m : M.val.obj W) (n : N.val.obj W) :
    ((monoidalCategory R).tensorObj M N).val.obj W :=
  (tensorObjIsoSheafification M N).inv.val.app W
    (((PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
      (M.val ⊗ N.val)).app W (m ⊗ₜ[R.obj.obj W] n))

/-- The canonical bilinear pairing, as a presheaf morphism.
Source: Stacks 03EK (blueprint: def-weil-pbc-ringed-tensor-section-calculus). -/
private noncomputable def pureMap (M N : SheafOfModules.{u} (ringSheaf R)) :
    M.val ⊗ N.val ⟶ ((monoidalCategory R).tensorObj M N).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit.app
    (M.val ⊗ N.val) ≫ (tensorObjIsoSheafification M N).inv.val

/-- The identification `A ⊗ T ≅ a(A ⊗ T)` is natural in `T`. -/
private lemma whiskerLeft_tensorObjIsoSheafification_hom (A : SheafOfModules.{u} (ringSheaf R))
    {T T' : SheafOfModules.{u} (ringSheaf R)} (f : T ⟶ T') :
    A ◁ f ≫ (tensorObjIsoSheafification A T').hom =
      (tensorObjIsoSheafification A T).hom ≫ ((PresheafOfModules.sheafification (𝟙 (ringSheaf
        R).obj))).map (A.val ◁ f.val) := by
  have h := (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 ((ringSheaf
    R)).obj)).counit.naturality f
  dsimp at h
  simp only [tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom, tensorIso_inv,
    Iso.app_inv, asIso_inv, Functor.Monoidal.μIso_hom, Category.assoc,
    ← Functor.LaxMonoidal.μ_natural_right]
  simp only [← Category.assoc]
  congr 1
  rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  congr 1
  simp only [NatIso.isIso_inv_app, IsIso.eq_inv_comp]
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rfl

/-- The identification `A ⊗ T ≅ a(A ⊗ T)` is natural in `A`. -/
private lemma whiskerRight_tensorObjIsoSheafification_hom {A A' : SheafOfModules.{u} (ringSheaf R)}
    (f : A' ⟶ A) (T : SheafOfModules.{u} (ringSheaf R)) :
    f ▷ T ≫ (tensorObjIsoSheafification A T).hom =
      (tensorObjIsoSheafification A' T).hom ≫ ((PresheafOfModules.sheafification (𝟙 (ringSheaf
        R).obj))).map (f.val ▷ T.val) := by
  have h := (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 ((ringSheaf
    R)).obj)).counit.naturality f
  dsimp at h
  simp only [tensorObjIsoSheafification, Iso.trans_hom, Iso.symm_hom, tensorIso_inv,
    Iso.app_inv, asIso_inv, Functor.Monoidal.μIso_hom, Category.assoc,
    ← Functor.LaxMonoidal.μ_natural_left]
  simp only [← Category.assoc]
  congr 1
  rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  congr 1
  simp only [NatIso.isIso_inv_app, IsIso.eq_inv_comp]
  rw [← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rfl

private lemma tensorIso_natural
    {F F' G G' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : F ⟶ F') (g : G ⟶ G') :
    letI := monoidalCategory R
    (f ⊗ₘ g) ≫ (tensorObjIsoSheafification F' G').hom =
      (tensorObjIsoSheafification F G).hom ≫
        (PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map (f.val ⊗ₘ g.val) := by
  let := monoidalCategory R
  erw [tensorHom_def, Category.assoc,
    whiskerLeft_tensorObjIsoSheafification_hom (R := R) F' g,
    ← Category.assoc,
    whiskerRight_tensorObjIsoSheafification_hom (R := R) f G,
    Category.assoc, ← Functor.map_comp, ← tensorHom_def]

set_option backward.isDefEq.respectTransparency false in
/-- The presheaf pairing into the sheaf tensor is natural in both modules.
Source: Stacks Project, Modules on Sites, Tag 03EK
(blueprint: def-weil-pbc-ringed-tensor-section-calculus). -/
private theorem pureMap_natural
    {F F' G G' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)}
    (f : F ⟶ F') (g : G ⟶ G') :
    letI := monoidalCategory R
    pureMap R F G ≫ (f ⊗ₘ g).val =
      (f.val ⊗ₘ g.val) ≫ pureMap R F' G' := by
  let := monoidalCategory R
  have h : (tensorObjIsoSheafification F G).inv ≫ (f ⊗ₘ g) =
      (PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map (f.val ⊗ₘ g.val) ≫
        (tensorObjIsoSheafification F' G').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← tensorIso_natural, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hval := congrArg Hom.val h
  change (tensorObjIsoSheafification F G).inv.val ≫ (f ⊗ₘ g).val =
    ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map (f.val ⊗ₘ g.val)).val ≫
      (tensorObjIsoSheafification F' G').inv.val at hval
  let η := (PresheafOfModules.sheafificationAdjunction (𝟙 (ringSheaf R).obj)).unit
  have hn := η.naturality (f.val ⊗ₘ g.val)
  change (f.val ⊗ₘ g.val) ≫ η.app (F'.val ⊗ G'.val) =
    η.app (F.val ⊗ G.val) ≫
      ((PresheafOfModules.sheafification (𝟙 (ringSheaf R).obj)).map (f.val ⊗ₘ g.val)).val at hn
  unfold pureMap
  erw [Category.assoc, hval, ← Category.assoc, ← hn]
  rfl

/-- Tensor morphisms act componentwise on pure sections. Source: Stacks 03EK
(blueprint: def-weil-pbc-ringed-tensor-section-calculus). -/
private theorem pure_map {M M' N N' : SheafOfModules.{u} (ringSheaf R)}
    (f : M ⟶ M') (g : N ⟶ N') (W : Cᵒᵖ) (m : M.val.obj W) (n : N.val.obj W) :
    ((monoidalCategory R).tensorHom f g).val.app W (pure R M N W m n) =
      pure R M' N' W (f.val.app W m) (g.val.app W n) := by
  exact congrArg (fun k ↦ k.app W (m ⊗ₜ[R.obj.obj W] n)) (pureMap_natural R f g)
end Pure
end SheafOfModules.CochainScalarConstruction

namespace SheafOfModules.CochainInversePairing
open SheafOfModules.CochainScalarConstruction
attribute [local irreducible] monoidalCategory
attribute [local instance 2000] cochainModulesMonoidal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

omit [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
omit [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
omit [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
omit [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
omit [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
omit [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
omit [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
omit [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
omit [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
omit [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
end SheafOfModules.CochainInversePairing

namespace SheafOfModules.CochainInversePairing
open SheafOfModules.CochainGeometricConstruction SheafOfModules.GeometricConstruction
open SheafOfModules.CochainScalarConstruction
attribute [local irreducible] monoidalCategory
attribute [local instance 2000] cochainModulesMonoidal
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
variable (R : Sheaf J CommRingCat.{u}) (RI : Sheaf K CommRingCat.{u})
  (F : Sheaf J (Type u) ⥤ Sheaf K (Type u))
  (V : Sheaf K (Type u) ⥤ Sheaf J (Type u))
  (adj : F ⊣ V) [PreservesFiniteLimits F]
  (I : AlgebraicInverseImage F R RI)

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
variable [PreservesFiniteLimits V]

omit [PreservesFiniteLimits F] in
omit [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
omit [PreservesFiniteLimits F] in
omit [PreservesFiniteLimits F] in
omit [PreservesFiniteLimits F] in
omit [PreservesFiniteLimits F] in
omit [PreservesFiniteLimits F] [PreservesFiniteLimits V] in
omit [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
set_option backward.isDefEq.respectTransparency false in
omit [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
set_option backward.isDefEq.respectTransparency false in
omit [PreservesFiniteLimits F] [PreservesFiniteLimits V] in
attribute [local irreducible] CochainScalarConstruction.pure

-- The tensor construction is already locally irreducible.

set_option maxHeartbeats 800000 in
-- The proof checks transported module structures in four bilinear identities and two inverses.
end SheafOfModules.CochainInversePairing

namespace SheafOfModules.CochainInversePairing
attribute [local irreducible] monoidalCategory
attribute [local instance 2000] cochainModulesMonoidal
open SheafOfModules.CochainScalarConstruction
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  [EssentiallySmall.{u} C] [EssentiallySmall.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (R : Sheaf J CommRingCat.{u}) (RI : Sheaf K CommRingCat.{u})
  (uInv : Sheaf J (Type u) ⥤ Sheaf K (Type u))
  (I : AlgebraicInverseImage uInv R RI)

set_option quotPrecheck false
set_option hygiene false in
local notation "𝓡" R =>
  (sheafCompose _ (forget₂ CommRingCat.{u} RingCat.{u})).obj R
set_option hygiene false in
local notation "𝓤" R =>
  (toSheaf (𝓡 R) ⋙ sheafCompose _ (CategoryTheory.forget AddCommGrpCat.{u}))

end SheafOfModules.CochainInversePairing
