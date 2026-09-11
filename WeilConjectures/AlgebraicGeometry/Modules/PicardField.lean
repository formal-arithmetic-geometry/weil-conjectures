/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.Topology.Sheaves.PUnit
public import WeilConjectures.AlgebraicGeometry.Modules.Picard

/-!
# Line bundles on the spectrum of a field are trivial

Let `X` be a scheme whose underlying topological space has at most one point, e.g. the spectrum
of a field. Then the only open subsets of `X` are `⊥` and `⊤`, the sections of any `𝒪ₓ`-module
over `⊥` are zero, and every presheaf of `𝒪ₓ`-modules is automatically a sheaf. Consequently the
functor of sections over `⊤` is monoidal, and it identifies invertible `𝒪ₓ`-modules with
invertible `Γ(X, ⊤)`-modules. When `Γ(X, ⊤)` is a local ring, for instance when `X = Spec K` for
a field `K`, invertible modules over it are free of rank one, and we conclude that every line
bundle on `X` is trivial.

## Main results

- `AlgebraicGeometry.Scheme.Modules.nonempty_iso_tensorUnit_of_invertible`: on a scheme with at
  most one point whose ring of global sections is local, in particular on the spectrum of a
  field, every invertible sheaf of modules is isomorphic to the structure sheaf.
- `AlgebraicGeometry.Scheme.subsingleton_pic` and
  `AlgebraicGeometry.Scheme.subsingleton_pic_spec_field`: the Picard group of such a scheme, in
  particular of the spectrum of a field, is trivial.

-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

section Sections

instance subsingleton_sections_bot (M : X.Modules) : Subsingleton Γ(M, ⊥) :=
  Module.subsingleton Γ(X, ⊥) Γ(M, ⊥)

/-- On a scheme with at most one point, a morphism of `𝒪ₓ`-modules is an isomorphism as soon as
it is one on sections over `⊤`: the only other open subset is `⊥`, where all sections vanish. -/
theorem isIso_of_isIso_app_top [Subsingleton X] {M N : X.Modules} (φ : M ⟶ N)
    (h : IsIso (φ.app ⊤)) : IsIso φ := by
  rw [Hom.isIso_iff_isIso_app]
  intro U
  rcases U.eq_bot_or_top with rfl | rfl
  · rw [ConcreteCategory.isIso_iff_bijective]
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩
  · exact h

end Sections

section Sheafification

variable (P : _root_.PresheafOfModules.{u} (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat.{u}))

/-- On a scheme with at most one point, every presheaf of `𝒪ₓ`-modules is a sheaf: the only
open subsets are `⊥` and `⊤`, and the sections over `⊥` form the zero module. -/
theorem isSheaf_presheaf [Subsingleton X] :
    TopCat.Presheaf.IsSheaf (X := X) P.presheaf := by
  refine TopCat.Presheaf.isSheaf_of_isTerminal_of_indiscrete (IndiscreteTopology.eq_top _) _ ?_
  have h : Subsingleton (P.obj (.op ⊥)) := Module.subsingleton Γ(X, ⊥) _
  exact (@AddCommGrpCat.isZero_of_subsingleton _ h).isTerminal

/-- On a scheme with at most one point, the unit of the sheafification adjunction for presheaves
of modules is an isomorphism. -/
theorem isIso_sheafificationAdjunction_unit_app [Subsingleton X] :
    IsIso ((_root_.PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).unit.app P) := by
  have h₁ : IsIso (toSheafify (Opens.grothendieckTopology X) P.presheaf) :=
    isIso_toSheafify _ (isSheaf_presheaf P)
  have h₂ : IsIso ((_root_.PresheafOfModules.toPresheaf _).map
      ((_root_.PresheafOfModules.sheafificationAdjunction
        (𝟙 X.ringCatSheaf.obj)).unit.app P)) := by
    rw [_root_.PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact h₁
  exact isIso_of_reflects_iso _ (_root_.PresheafOfModules.toPresheaf _)

/-- On a scheme with at most one point, a presheaf of `𝒪ₓ`-modules is isomorphic to its
sheafification. -/
noncomputable def sheafificationUnitIso [Subsingleton X] :
    P ≅ (SheafOfModules.forget _).obj ((SheafOfModules.sheafification X.sheaf).obj P) :=
  have := isIso_sheafificationAdjunction_unit_app P
  asIso ((_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P)

end Sheafification

section Tensor

/-- An `𝒪ₓ`-module is the sheafification of its underlying presheaf of modules. -/
noncomputable def sheafificationCounitIso (M : X.Modules) :
    (SheafOfModules.sheafification X.sheaf).obj ((SheafOfModules.forget _).obj M) ≅ M :=
  (asIso (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).app M

/-- The tensor product of two `𝒪ₓ`-modules is the sheafification of the presheaf tensor product
of their underlying presheaves of modules. -/
noncomputable def tensorIsoSheafification (M N : X.Modules) :
    M ⊗ N ≅ (SheafOfModules.sheafification X.sheaf).obj
      ((SheafOfModules.forget _).obj M ⊗ (SheafOfModules.forget _).obj N) :=
  ((sheafificationCounitIso M).symm ⊗ᵢ (sheafificationCounitIso N).symm) ≪≫
    Functor.Monoidal.μIso (SheafOfModules.sheafification X.sheaf) _ _

/-- On a scheme with at most one point, the sections over `⊤` of a tensor product of
`𝒪ₓ`-modules are the tensor product of the sections over `⊤`. -/
noncomputable def tensorSectionsTopIso [Subsingleton X] (M N : X.Modules) :
    (M ⊗ N).val.obj (.op ⊤) ≅ M.val.obj (.op ⊤) ⊗ N.val.obj (.op ⊤) :=
  (SheafOfModules.evaluation _ (.op ⊤)).mapIso (tensorIsoSheafification M N) ≪≫
    (_root_.PresheafOfModules.evaluation _ (.op ⊤)).mapIso
      (sheafificationUnitIso
        ((SheafOfModules.forget _).obj M ⊗ (SheafOfModules.forget _).obj N)).symm

variable (X) in
/-- The sections over `⊤` of the tensor unit of `X.Modules` form the ring `Γ(X, ⊤)`. -/
noncomputable def tensorUnitSectionsTopIso :
    (𝟙_ X.Modules).val.obj (.op ⊤) ≅ ModuleCat.of Γ(X, ⊤) Γ(X, ⊤) :=
  (SheafOfModules.evaluation _ (.op ⊤)).mapIso (SheafOfModules.tensorUnitIso X.sheaf)

/-- On a scheme with at most one point, the sections over `⊤` of an invertible `𝒪ₓ`-module form
an invertible `Γ(X, ⊤)`-module. -/
theorem module_invertible_sections_top [Subsingleton X] {M : X.Modules}
    (hM : M.Invertible) : Module.Invertible Γ(X, ⊤) Γ(M, ⊤) := by
  obtain ⟨N, ⟨e⟩⟩ := (SheafOfModules.invertible_iff_exists (R := X.sheaf)).1 hM
  exact .left (((tensorSectionsTopIso M N).symm ≪≫
    (SheafOfModules.evaluation _ (.op ⊤)).mapIso e ≪≫ tensorUnitSectionsTopIso X).toLinearEquiv)

end Tensor

section OfSection

/-- The section of an `𝒪ₓ`-module determined by a global section, i.e. a section over `⊤`. -/
noncomputable def sectionsOfTop (M : X.Modules) (m : Γ(M, ⊤)) : M.sections :=
  _root_.PresheafOfModules.sectionsMk (fun _ ↦ M.val.map (homOfLE le_top).op m)
    (fun _ _ _ ↦ by
      rw [← _root_.PresheafOfModules.map_comp_apply]
      exact M.val.congr_map_apply (Subsingleton.elim _ _) m)

/-- The morphism from the free `𝒪ₓ`-module of rank one to `M` determined by a global section
of `M`. -/
noncomputable def homOfSectionTop (M : X.Modules) (m : Γ(M, ⊤)) :
    SheafOfModules.unit X.ringCatSheaf ⟶ M :=
  M.unitHomEquiv.symm (sectionsOfTop M m)

theorem homOfSectionTop_app_top_one (M : X.Modules) (m : Γ(M, ⊤)) :
    (homOfSectionTop M m).val.app (.op ⊤) (1 : Γ(X, ⊤)) = m := by
  have h := SheafOfModules.unitHomEquiv_apply_coe M (homOfSectionTop M m) (.op ⊤)
  rw [← h, homOfSectionTop, Equiv.apply_symm_apply]
  simp [sectionsOfTop]

@[simp]
theorem homOfSectionTop_app_top (M : X.Modules) (m : Γ(M, ⊤)) (r : Γ(X, ⊤)) :
    (homOfSectionTop M m).val.app (.op ⊤) r = r • m := by
  have h := ((homOfSectionTop M m).val.app (.op ⊤)).hom.map_smul r (1 : Γ(X, ⊤))
  rw [smul_eq_mul, mul_one] at h
  rw [h, homOfSectionTop_app_top_one]

/-- On a scheme with at most one point, an `𝒪ₓ`-module whose global sections are free of rank
one is isomorphic to the free `𝒪ₓ`-module of rank one. -/
theorem nonempty_iso_unit_of_linearEquiv [Subsingleton X] (M : X.Modules)
    (f : Γ(M, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤)) :
    Nonempty (SheafOfModules.unit X.ringCatSheaf ≅ M) := by
  have hfun : ∀ r : Γ(X, ⊤), Hom.app (homOfSectionTop M (f.symm 1)) ⊤ r = f.symm r := by
    intro r
    change (homOfSectionTop M (f.symm 1)).val.app (.op ⊤) r = _
    have hr : f.symm r = r • f.symm 1 := by
      rw [← LinearEquiv.map_smul, smul_eq_mul, mul_one]
    rw [homOfSectionTop_app_top, hr]
  have h : IsIso (Hom.app (homOfSectionTop M (f.symm 1)) ⊤) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    have : ⇑(Hom.app (homOfSectionTop M (f.symm 1)) ⊤) = ⇑f.symm := funext hfun
    rw [this]
    exact f.symm.bijective
  have := isIso_of_isIso_app_top _ h
  exact ⟨asIso (homOfSectionTop M (f.symm 1))⟩

end OfSection

section Main

/-- On a scheme `X` with at most one point whose ring of global sections is local — for instance
the spectrum of a field — every invertible `𝒪ₓ`-module is isomorphic to the structure sheaf. -/
theorem nonempty_iso_tensorUnit_of_invertible [Subsingleton X]
    [IsLocalRing Γ(X, ⊤)] {M : X.Modules} (hM : M.Invertible) :
    Nonempty (M ≅ 𝟙_ X.Modules) := by
  have := module_invertible_sections_top hM
  obtain ⟨f⟩ := Module.Invertible.free_iff_linearEquiv.1
    (inferInstance : Module.Free Γ(X, ⊤) Γ(M, ⊤))
  obtain ⟨e⟩ := nonempty_iso_unit_of_linearEquiv M f
  exact ⟨e.symm ≪≫ (SheafOfModules.tensorUnitIso X.sheaf).symm⟩

end Main

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- The Picard group of a scheme with at most one point whose ring of global sections is local
is trivial. -/
theorem subsingleton_pic [Subsingleton X] [IsLocalRing Γ(X, ⊤)] :
    Subsingleton X.Pic := by
  have h : Subsingleton (Skeleton X.Modules)ˣ :=
    subsingleton_of_forall_eq 1 fun u ↦ Units.ext <| by
      have hu : ((fromSkeleton X.Modules).obj (u : Skeleton X.Modules)).Invertible := by
        change IsUnit (toSkeleton ((fromSkeleton X.Modules).obj (u : Skeleton X.Modules)))
        rw [toSkeleton_fromSkeleton_obj]
        exact u.isUnit
      calc (u : Skeleton X.Modules)
          = toSkeleton ((fromSkeleton X.Modules).obj (u : Skeleton X.Modules)) :=
            (toSkeleton_fromSkeleton_obj _).symm
        _ = toSkeleton (𝟙_ X.Modules) :=
            toSkeleton_eq_toSkeleton_iff.2 (Modules.nonempty_iso_tensorUnit_of_invertible hu)
        _ = 1 := Skeleton.one_eq.symm
  exact h

instance isLocalRing_sections_top_spec (R : CommRingCat.{u}) [IsLocalRing R] :
    IsLocalRing Γ(Spec R, ⊤) :=
  ((ΓSpecIso R).commRingCatIsoToRingEquiv).symm.isLocalRing

/-- The Picard group of the spectrum of a field is trivial: every line bundle on `Spec K` is
trivial. -/
instance subsingleton_pic_spec_field {K : Type u} [Field K] :
    Subsingleton (Spec (CommRingCat.of K)).Pic :=
  subsingleton_pic

end AlgebraicGeometry.Scheme
