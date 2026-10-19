/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import WeilConjectures.CategoryTheory.Sites.WeaklyContractible
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! # Projectivity of the regular module on a weakly contractible scheme

Source: Stacks Project, sites-cohomology.tex, Tag 0946; proetale.tex, Tag 09C3
(blueprint: lem-sf-weakly-contractible-unit-projective).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The regular module sheaf is projective on a weakly contractible scheme.

Source: Stacks Project, sites-cohomology.tex, Tag 0946; the regular-module Hom
calculation in proetale.tex, Tag 09C3
(blueprint: lem-sf-weakly-contractible-unit-projective).

Proof: a map from the regular module is determined by the section which is the
image of 1. Forget an epimorphism of module sheaves to a locally surjective map of
set sheaves. Weak contractibility lifts that section over the terminal site object.
Restriction of its lift defines a compatible global section, hence a module map.
Naturality proves that its composite with the epimorphism is the prescribed map. -/
private theorem unit_projective_of_weakly_contractible
    (S : Scheme.{u})
    (hw : (ProEt.topology S).IsWeaklyContractible.{u + 1} (ProEt.mk (𝟙 S)))
    (R : Sheaf (ProEt.topology S) RingCat.{u + 1}) :
    Projective (SheafOfModules.unit.{u, u + 1, u + 1} R) := by
  have : PreservesFiniteColimits (SheafOfModules.toSheaf.{u + 1} R) :=
    (moduleSheaves_colimits_forgetful.{u + 1, u, u + 1, u + 1} R).2.2.1
  constructor
  intro M N f p hp
  let W : S.ProEt := ProEt.mk (𝟙 S)
  let p' := (sheafCompose (ProEt.topology S) (forget AddCommGrpCat.{u + 1})).map
    ((SheafOfModules.toSheaf.{u + 1} R).map p)
  have : Epi ((SheafOfModules.toSheaf.{u + 1} R).map p) := inferInstance
  have hsurj : Function.Surjective (p'.hom.app (op W)) :=
    hw p' ((Presheaf.isLocallySurjective_iff_whisker_forget _ _).mp
      ((Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u + 1}
        ((SheafOfModules.toSheaf.{u + 1} R).map p)).mpr inferInstance))
  change Function.Surjective (p.val.app (op W)) at hsurj
  obtain ⟨x, hx⟩ := hsurj (f.val.app (op W) (show R.obj.obj (op W) from 1))
  let w (U : S.ProEt) : U ⟶ W := MorphismProperty.Over.homMk U.hom (by exact Category.comp_id _)
  let s : M.sections := PresheafOfModules.sectionsMk
    (fun U ↦ M.val.map (w U.unop).op x) (by
      intro U V g
      rw [← M.val.map_comp_apply]
      have he : (w U.unop).op ≫ g = (w V.unop).op := by
        apply Quiver.Hom.unop_inj
        apply MorphismProperty.Over.Hom.ext
        change g.unop.left ≫ U.unop.hom = V.unop.hom
        exact MorphismProperty.Over.w g.unop
      rw [he])
  refine ⟨M.unitHomEquiv.symm s, ?_⟩
  apply N.unitHomEquiv.injective
  rw [SheafOfModules.unitHomEquiv_symm_comp, Equiv.apply_symm_apply]
  apply PresheafOfModules.sections_ext
  intro U
  change p.val.app U (M.val.map (w U.unop).op x) = f.val.app U (show R.obj.obj U from 1)
  rw [PresheafOfModules.naturality_apply, hx]
  have hf := PresheafOfModules.naturality_apply f.val (w U.unop).op
    (1 : R.obj.obj (op W))
  change f.val.app U (R.obj.map (w U.unop).op 1) =
    N.val.map (w U.unop).op
      (f.val.app (op W) (show R.obj.obj (op W) from 1)) at hf
  simpa only [map_one] using hf.symm

/-- Finite powers of the regular module are projective by the biproduct property.
Source: Stacks Project, proetale.tex, Tag 09C3
(blueprint: lem-sf-weakly-contractible-unit-projective). -/
theorem finitePower_unit_projective_of_weaklyContractible
    (S : Scheme.{u})
    (hw : (ProEt.topology S).IsWeaklyContractible.{u + 1} (ProEt.mk (𝟙 S)))
    (R : Sheaf (ProEt.topology S) RingCat.{u + 1}) (n : ℕ) :
    Projective (∏ᶜ fun _ : Fin n ↦ SheafOfModules.unit.{u, u + 1, u + 1} R) := by
  have : Projective (SheafOfModules.unit.{u, u + 1, u + 1} R) :=
    unit_projective_of_weakly_contractible S hw R
  have : HasFiniteProducts (SheafOfModules.{u + 1} R) := inferInstance
  have : HasFiniteBiproducts (SheafOfModules.{u + 1} R) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let g : Fin n → SheafOfModules.{u + 1} R :=
    fun _ ↦ SheafOfModules.unit.{u, u + 1, u + 1} R
  have : ∀ i : Fin n, Projective (g i) := fun _ ↦
    unit_projective_of_weakly_contractible S hw R
  have hp : Projective (⨁ g) := by
    constructor
    intro M N f p hp
    refine ⟨biproduct.desc (fun i ↦
      Projective.factorThru (biproduct.ι g i ≫ f) p), ?_⟩
    apply biproduct.hom_ext'
    intro i
    simp only [biproduct.ι_desc_assoc, Projective.factorThru_comp]
  exact Projective.of_iso (biproduct.isoProduct g) hp

end WeilConjectures
