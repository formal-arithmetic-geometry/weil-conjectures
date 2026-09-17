/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono

/-!
# The forgetful functor from sheaves of modules to abelian sheaves is exact

Mathlib knows that `SheafOfModules.toSheaf R : SheafOfModules R ⥤ Sheaf J AddCommGrpCat`
preserves finite limits. Here we show that it also preserves epimorphisms, and deduce that
it sends short exact sequences of sheaves of modules to short exact sequences of abelian
sheaves and that a morphism of sheaves of modules is an epimorphism precisely when it is
locally surjective.

A cokernel in `SheafOfModules R` is the sheafification of the cokernel computed in
`PresheafOfModules R.val`, and likewise in `Sheaf J AddCommGrpCat`; the two sheafifications
are compared by `PresheafOfModules.sheafificationCompToSheaf`.

## Main results

- `SheafOfModules.toSheaf_preservesEpimorphisms`
- `SheafOfModules.epi_iff_isLocallySurjective`
- `CategoryTheory.ShortComplex.ShortExact.map_toSheaf`

-/

@[expose] public section

universe v v' u u'

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

private lemma epi_of_epi_comp_isIso {D : Type*} [Category D] [Limits.HasZeroMorphisms D]
    {X Y Z : D} (a : X ⟶ Y) (b : Y ⟶ Z) [IsIso b] (h : Epi (a ≫ b)) : Epi a := by
  have : Epi ((a ≫ b) ≫ inv b) := epi_comp _ _
  simpa using this

open PresheafOfModules in
/-- The image under `SheafOfModules.toSheaf` of an epimorphism which is the sheafification of
a morphism of presheaves of modules is an epimorphism. -/
private lemma epi_toSheaf_map_sheafification_map {P Q : PresheafOfModules.{v} R.obj} (ψ : P ⟶ Q)
    (h : Epi ((sheafification (𝟙 R.obj)).map ψ)) :
    Epi ((toSheaf R).map ((sheafification (𝟙 R.obj)).map ψ)) := by
  have h₁ : IsZero (cokernel ((sheafification (𝟙 R.obj)).map ψ)) := isZero_cokernel_of_epi _
  have h₂ : IsZero ((sheafification (𝟙 R.obj)).obj (cokernel ψ)) :=
    h₁.of_iso (PreservesCokernel.iso _ ψ)
  have h₃ : IsZero ((sheafification (𝟙 R.obj) ⋙ toSheaf R).obj (cokernel ψ)) :=
    Functor.map_isZero (toSheaf R) h₂
  have e₀ := (sheafificationCompToSheaf (𝟙 R.obj)).app (cokernel ψ)
  have e₁ := (presheafToSheaf J AddCommGrpCat.{v}).mapIso
    (PreservesCokernel.iso (toPresheaf R.obj) ψ)
  have e₂ := PreservesCokernel.iso (presheafToSheaf J AddCommGrpCat.{v})
    ((toPresheaf R.obj).map ψ)
  exact Preadditive.epi_of_isZero_cokernel _ (h₃.of_iso (e₀ ≪≫ e₁ ≪≫ e₂).symm)

instance toSheaf_preservesEpimorphisms : (toSheaf.{v} R).PreservesEpimorphisms where
  preserves {M N} g hg := by
    have adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
    have hnat : (PresheafOfModules.sheafification (𝟙 R.obj)).map
          ((SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).map g) ≫
          adj.counit.app N = adj.counit.app M ≫ g := adj.counit.naturality g
    have h₁ : Epi ((PresheafOfModules.sheafification (𝟙 R.obj)).map
        ((SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)).map g) ≫
        adj.counit.app N) := by
      rw [hnat]; exact epi_comp _ _
    have h₂ := epi_toSheaf_map_sheafification_map _ (epi_of_epi_comp_isIso _ _ h₁)
    have h₃ : Epi ((toSheaf R).map (adj.counit.app M) ≫ (toSheaf R).map g) := by
      rw [← Functor.map_comp, ← hnat, Functor.map_comp]
      have := h₂
      exact epi_comp _ _
    exact epi_of_epi ((toSheaf R).map (adj.counit.app M)) _

/-- **A morphism of sheaves of modules is an epimorphism exactly when it is locally
surjective.** Being an epimorphism of sheaves is not being surjective on sections: it only
means that every section of the target is locally in the image. -/
theorem epi_iff_isLocallySurjective {M N : SheafOfModules.{v} R} (φ : M ⟶ N) :
    Epi φ ↔ Sheaf.IsLocallySurjective ((toSheaf R).map φ) :=
  ⟨fun _ ↦ (Sheaf.isLocallySurjective_iff_epi' _ _).mpr ((toSheaf R).map_epi φ),
    fun h ↦ (toSheaf R).epi_of_epi_map ((Sheaf.isLocallySurjective_iff_epi' _ _).mp h)⟩

end SheafOfModules

namespace CategoryTheory.ShortComplex.ShortExact

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}} [HasSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- The forgetful functor from sheaves of modules to sheaves of abelian groups sends short
exact sequences to short exact sequences. -/
lemma map_toSheaf {S : ShortComplex (SheafOfModules.{v} R)} (hS : S.ShortExact) :
    (S.map (SheafOfModules.toSheaf R)).ShortExact := by
  have := hS.epi_g
  have := hS.mono_f
  have h := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (SheafOfModules.toSheaf.{v} R)).1 inferInstance S hS
  exact { exact := h.1, mono_f := h.2, epi_g := (SheafOfModules.toSheaf R).map_epi _ }

end CategoryTheory.ShortComplex.ShortExact
