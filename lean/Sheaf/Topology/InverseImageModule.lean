/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.Ring.Colimits

/-!
# Module structure on the topological inverse image

Source: Stacks Project, Tags 008X and 008Y (blueprint: def-pc-topological-inverse-image-module).
The underlying abelian sheaf and ring sheaf use the explicit left-Kan-extension followed
by sheafification construction, rather than an abstract chosen left adjoint.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- Inverse image computed by presheaf inverse image and sheafification.
Source: Stacks, Tag 008X (blueprint: def-pc-topological-inverse-image-module). -/
def inverseImageConstruction (A : Type (u + 1)) [Category.{u} A]
    [HasColimits.{u} A] [HasWeakSheafify (Opens.grothendieckTopology X) A] :
    CategoryTheory.Sheaf (Opens.grothendieckTopology Y) A ⥤
      CategoryTheory.Sheaf (Opens.grothendieckTopology X) A :=
  Functor.sheafPullbackConstruction.sheafPullback (Opens.map f) A _ _

variable (R : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u})

/-- The inverse-image ring sheaf. Source: Stacks, Tag 008X
(blueprint: def-pc-topological-inverse-image-module). -/
def inverseImageRing := (inverseImageConstruction f CommRingCat.{u}).obj R

set_option hygiene false in
local notation "𝓡" R =>
  (sheafCompose (Opens.grothendieckTopology Y)
    (forget₂ CommRingCat.{u} RingCat.{u})).obj R

variable (M : SheafOfModules.{u} (𝓡 R))

/-- The abelian inverse image, before supplying its module structure. Source: Stacks, Tag 008X
(blueprint: def-pc-topological-inverse-image-module). -/
def inverseImageAb :=
  (inverseImageConstruction f AddCommGrpCat.{u}).obj ((SheafOfModules.toSheaf (𝓡 R)).obj M)

/-- The canonical module instances on the sections of the inverse image exist, are
compatible with restriction, and make the inverse-image unit semilinear.
Source: Stacks, Tag 008X (blueprint: def-pc-topological-inverse-image-module).
Proof: first form the colimits of the section rings and modules over opens containing
`f(U)`. Represent two germs over a common open and multiply their representatives there;
filteredness makes this independent of representatives and proves the module laws.
Sheafification extends this action uniquely by local representatives (Stacks 0089).
Restriction and the unit preserve these representatives, giving the two asserted laws. -/
theorem exists_inverseImageModuleInstances :
    ∃ d : ∀ U : (Opens X)ᵒᵖ,
      Module ((inverseImageRing f R).obj.obj U) ((inverseImageAb f R M).obj.obj U),
      (letI := d
       ∀ {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
         (r : (inverseImageRing f R).obj.obj U) (m : (inverseImageAb f R M).obj.obj U),
         (inverseImageAb f R M).obj.map i (r • m) =
           (inverseImageRing f R).obj.map i r • (inverseImageAb f R M).obj.map i m) ∧
      (letI := d
       ∀ (V : (Opens Y)ᵒᵖ) (r : R.obj.obj V) (m : M.val.obj V),
         ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
           (Opens.map f) AddCommGrpCat.{u}
           (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).unit.app
             ((SheafOfModules.toSheaf (𝓡 R)).obj M)).hom.app V (r • m) =
         @SMul.smul _ _ (d ((Opens.map f).op.obj V)).toSMul
         (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
           (Opens.map f) CommRingCat.{u}
           (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).unit.app R).hom.app V r)
         (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
           (Opens.map f) AddCommGrpCat.{u}
           (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).unit.app
             ((SheafOfModules.toSheaf (𝓡 R)).obj M)).hom.app V m)) := by
  sorry

/-- Canonical section module instances, supplied by the preceding existence theorem.
Source: Stacks, Tag 008X (blueprint: def-pc-topological-inverse-image-module). -/
@[instance_reducible]
def inverseImageModuleInstances (U : (Opens X)ᵒᵖ) :
    Module ((inverseImageRing f R).obj.obj U) ((inverseImageAb f R M).obj.obj U) :=
  Classical.choose (exists_inverseImageModuleInstances f R M) U

attribute [local instance] inverseImageModuleInstances

/-- The inverse-image module, with the actual abelian inverse-image sections and restrictions.
Source: Stacks, Tag 008X (blueprint: def-pc-topological-inverse-image-module). -/
def inverseImageModule : SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj (inverseImageRing f R)) where
  val := @PresheafOfModules.ofPresheaf _ _ _ (inverseImageAb f R M).obj
    (inverseImageModuleInstances f R M)
    (fun {_ _} i r m ↦
      (Classical.choose_spec (exists_inverseImageModuleInstances f R M)).1 i r m)
  isSheaf := (inverseImageAb f R M).property

/-- The inverse image of a linear map is linear for the canonical instances.
Source: Stacks, Tag 008X (blueprint: def-pc-topological-inverse-image-module).
Proof: on local representatives this is the original linearity identity; the inverse
image map is induced by the colimit map followed by sheafification. Equality is local,
so the identity descends to all sections. -/
theorem inverseImageMap_smul {N : SheafOfModules.{u} (𝓡 R)} (a : M ⟶ N)
    (U : (Opens X)ᵒᵖ) (r : (inverseImageRing f R).obj.obj U)
    (m : (inverseImageModule f R M).val.obj U) :
    ((inverseImageConstruction f AddCommGrpCat.{u}).map
      ((SheafOfModules.toSheaf (𝓡 R)).map a)).hom.app U
      (@SMul.smul _ _ (inverseImageModuleInstances f R M U).toSMul r m) =
    @SMul.smul _ _ (inverseImageModuleInstances f R N U).toSMul r
      (((inverseImageConstruction f AddCommGrpCat.{u}).map
      ((SheafOfModules.toSheaf (𝓡 R)).map a)).hom.app U m) := by
  sorry

/-- Inverse image on module morphisms, using the inverse image on abelian sheaves.
Source: Stacks, Tag 008X (blueprint: def-pc-topological-inverse-image-module). -/
def inverseImageModuleMap {N : SheafOfModules.{u} (𝓡 R)} (a : M ⟶ N) :
    inverseImageModule f R M ⟶ inverseImageModule f R N :=
  ⟨PresheafOfModules.homMk
    ((inverseImageConstruction f AddCommGrpCat.{u}).map
      ((SheafOfModules.toSheaf (𝓡 R)).map a)).hom (inverseImageMap_smul f R M a)⟩

end
end TopCat.Sheaf
