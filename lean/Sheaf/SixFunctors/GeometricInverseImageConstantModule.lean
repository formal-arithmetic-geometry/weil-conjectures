/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.CategoryTheory.ConstantLeftModuleInverseImage
public import Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Geometric inverse image preserves constant module sheaves

Source: Stacks Project, `sites.tex`, Tags 0H7J and 00YV
(blueprint: lem-sfb-geometric-inverse-image-constant-module).

The constant module sheaf is represented by `siteConstantModuleFunctorGeneral`. The
recorded geometric-morphism lift supplies the module inverse image and its underlying
set comparison; the theorem states the resulting canonical constant-module
isomorphisms and their naturality in the coefficient module.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- The underlying set sheaf of the genuine constant module sheaf, identified with
set-valued constant sheafification by the canonical forgetful comparison.
Source: Stacks Project, Sites, 00YR and 0H7J; Modules on Sites, 03CY
(blueprint: lem-sfb-geometric-inverse-image-constant-module). -/
def constantModuleUnderlyingSetIso
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Type u) [CommRing R] [HasWeakSheafify J RingCat.{u}]
    (M : ModuleCat.{u} R) :
    (ConstantLeftModuleInverseImage.W J R).obj
        ((siteConstantModuleFunctorGeneral J R).obj M) ≅
      (constantSheaf J (Type u)).obj M :=
  (constantCommuteCompose J (forget AddCommGrpCat.{u})).app
    ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).obj M)

/-- The summand labelled by `m` in the underlying constant module sheaf: first take
constant set sheafification of the map from a singleton with value `m`, then use the
canonical module/set sheafification comparison.
Source: Stacks Project, Sites, 0H7J; Modules on Sites, 03CY
(blueprint: lem-sfb-geometric-inverse-image-constant-module). -/
def constantModuleSetSection
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Type u) [CommRing R] [HasWeakSheafify J RingCat.{u}]
    (M : ModuleCat.{u} R) (m : M) :
    (constantSheaf J (Type u)).obj PUnit.{u+1} ⟶
      (ConstantLeftModuleInverseImage.W J R).obj
        ((siteConstantModuleFunctorGeneral J R).obj M) :=
  (constantSheaf J (Type u)).map (TypeCat.ofHom (fun _ : PUnit.{u+1} ↦ m)) ≫
    (constantModuleUnderlyingSetIso J R M).inv

/-- Geometric inverse image preserves genuine constant module sheaves, naturally in
all linear maps, with the underlying comparison normalized on each constant section.

Source: Stacks Project, Sites, Tags 0H7J and 00YV
(blueprint: lem-sfb-geometric-inverse-image-constant-module).

Proof (the five steps of the node):
1. By `def-weil-pbc-constant-sheaf` and `def-weil-pbc-sheafification`, maps from the
constant set sheaf of `E` to a sheaf are families of maps from the terminal sheaf,
indexed by `E`. Thus it is the coproduct of `E` terminal sheaves, including `E` empty.
Its inclusions are the constant sections, and a set map carries the labelled inclusion
to the inclusion with its image label.
2. The adjunction makes `L` preserve these coproducts, by
`lem-weil-pbc-left-adjoint-preserves-colimits`. Finite-limit preservation identifies
`L` of the terminal sheaf with the terminal sheaf. The coproduct universal property
gives the unique isomorphism preserving every labelled inclusion, naturally in set maps.
3. By `lem-weil-pbc-sheafification-sets-exact`, constant sheafification preserves
finite products. Naturality for the projections gives compatibility of the comparison
with products. The underlying module and ring sheaves are these constant set sheaves,
with their units, by `lem-cbc-module-sheafification-underlying-sets` and
`lem-pc-sites-sheafification-underlying-sets`.
4. In `lem-pe-constant-left-module-inverse-image` the lifted operations come from `L`.
Naturality for addition, zero, negation, and scalar multiplication makes the set
comparison linear; `lem-pc-sites-module-sheafification-interface` identifies the genuine
constant-module action. Its ring comparison agrees with the recorded one because both
preserve scalar inclusions. The inverse comparison is linear as well.
5. Apply set naturality to each linear map to obtain the displayed module naturality.
The last equation is precisely the labelled-inclusion characterization in step 2,
using the dependency's `moduleSetIso` to forget module inverse image and `pointIso`
to identify inverse image of the terminal sheaf. -/
theorem geometric_inverse_image_constant_module
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (R : Type u) [CommRing R]
    [HasWeakSheafify J RingCat.{u}] [HasWeakSheafify K RingCat.{u}]
    (L : Sheaf J (Type u) ⥤ Sheaf K (Type u))
    (Rfun : Sheaf K (Type u) ⥤ Sheaf J (Type u))
    (adj : L ⊣ Rfun) (hL : PreservesFiniteLimits L) :
    ∃ d : ConstantLeftModuleInverseImageData.{u, w} J K R L Rfun adj hL,
      ∃ e : ∀ M : ModuleCat.{u} R,
        d.moduleFunctor.obj ((siteConstantModuleFunctorGeneral J R).obj M) ≅
          (siteConstantModuleFunctorGeneral K R).obj M,
        (∀ (M N : ModuleCat.{u} R) (f : M ⟶ N),
          d.moduleFunctor.map ((siteConstantModuleFunctorGeneral J R).map f) ≫ (e N).hom =
            (e M).hom ≫ (siteConstantModuleFunctorGeneral K R).map f) ∧
        (∀ (M : ModuleCat.{u} R) (m : M),
          L.map (constantModuleSetSection J R M m) ≫
              d.moduleSetIso.inv.app ((siteConstantModuleFunctorGeneral J R).obj M) ≫
              (ConstantLeftModuleInverseImage.W K R).map (e M).hom =
            d.pointIso.hom ≫ constantModuleSetSection K R M m) := by
  sorry

end CategoryTheory
