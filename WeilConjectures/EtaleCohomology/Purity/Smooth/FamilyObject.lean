/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Basic

/-!
# The family object of the deformation to the normal cone

For a deformation datum `D` of a closed section `s` of a smooth `g : V ⟶ B`
(`AlgebraicGeometry.Scheme.Hom.DeformationToNormalConeData`), the *family object* is the section
invariant `ℱ = Ls̃^* ω_{g̃}` of the pair `(g̃, s̃)`. Its fibres over `t = 1` and `t = 0` are the
section invariants of `(g, s)` and of the normal cone with its zero section: this is smooth base
change for `R^!` (`sk-prop-cohsm` (c)) applied to the two cartesian fibre squares of the
deformation.

## Main statements

- `AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_oneSection_familyObject`
- `AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_zeroSection_familyObject`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {V B : Scheme.{u}}

/-- Base change of the dualizing complex of a smooth morphism along a cartesian square:
`Lg'^* ω_f ≅ ω_{f'}`. -/
lemma nonempty_iso_leftDerivedUpperStar_dualizingComplex {X Y X' Y' : Scheme.{u}} {d : ℕ}
    (f : X ⟶ Y) [IsSeparated f] [SmoothOfRelativeDimension d f] [HasCompactification f]
    [HasInvertibleExponent Λ X] {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g) [HasCompactification f'] :
    Nonempty ((L((g')^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex (ModuleCat.{u + 1} Λ) f) ≅
      dualizingComplex (ModuleCat.{u + 1} Λ) f') := by
  obtain ⟨e⟩ := nonempty_iso_leftDerivedUpperStar_comp_rightDerivedUpperShriek Λ (d := d) f sq
  obtain ⟨ι⟩ := nonempty_iso_leftDerivedUpperStar_unit (ModuleCat.{u + 1} Λ) g
  exact ⟨e.app (𝟙_ _) ≪≫ (rightDerivedUpperShriek _ f').mapIso ι⟩

section Datum

variable {d : ℕ} {g : V ⟶ B} {s : B ⟶ V} {N : Scheme.Hom.NormalConeData d s}
  (D : Scheme.Hom.DeformationToNormalConeData d g s N) [IsSeparated D.proj]
  [HasCompactification D.proj] [HasInvertibleExponent Λ D.scheme]

/-- Blueprint `sk-lem-geometry` (1), the fibre over `t = 1`: the restriction of the family
object `ℱ = Ls̃^* ω_{g̃}` along the unit section is the section invariant of `(g, s)`,

`Li₁^* ℱ ≃ 𝒞(g, s)`. -/
theorem nonempty_iso_leftDerivedUpperStar_oneSection_familyObject [HasCompactification g] :
    Nonempty ((L((AffineSpace.oneSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
        (sectionInvariant Λ D.proj D.sect) ≅ sectionInvariant Λ g s) := by
  obtain ⟨e⟩ := nonempty_iso_leftDerivedUpperStar_dualizingComplex Λ (d := d) D.proj
    D.isPullback_oneFibre
  exact ⟨((leftDerivedUpperStarComp _ (AffineSpace.oneSection _ B) D.sect).app _).symm ≪≫
    (leftDerivedUpperStarComp _ s D.oneFibre _ D.comp_oneFibre.symm).app _ ≪≫
      (L((s)^*[ModuleCat.{u + 1} Λ])).mapIso e⟩

/-- Blueprint `sk-lem-geometry` (1), the fibre over `t = 0`: the restriction of the family
object along the zero section is the section invariant of the normal cone with its zero
section,

`Li₀^* ℱ ≃ 𝒞(π_N, 0_N)`. -/
theorem nonempty_iso_leftDerivedUpperStar_zeroSection_familyObject
    [HasCompactification N.proj] :
    Nonempty ((L((AffineSpace.zeroSection (ULift.{u} (Fin 1)) B)^*[ModuleCat.{u + 1} Λ])).obj
        (sectionInvariant Λ D.proj D.sect) ≅ sectionInvariant Λ N.proj N.zeroSection) := by
  obtain ⟨e⟩ := nonempty_iso_leftDerivedUpperStar_dualizingComplex Λ (d := d) D.proj
    D.isPullback_zeroFibre
  exact ⟨((leftDerivedUpperStarComp _ (AffineSpace.zeroSection _ B) D.sect).app _).symm ≪≫
    (leftDerivedUpperStarComp _ N.zeroSection D.zeroFibre _ D.comp_zeroFibre.symm).app _ ≪≫
      (L((N.zeroSection)^*[ModuleCat.{u + 1} Λ])).mapIso e⟩

end Datum

section Construction

variable {d : ℕ} (g : V ⟶ B) [IsSeparated g] [SmoothOfRelativeDimension d g]
  [HasCompactification g] [HasInvertibleExponent Λ V] (s : B ⟶ V) [IsClosedImmersion s]

include d in
/-- Blueprint `sk-lem-geometry` (3), the punctured trivialisation: over the punctured line
`j : 𝔾_{m,B} ⊆ 𝔸¹_B` the family object `ℱ = Ls̃^* ω_{g̃}` of the deformation space of `s` is
pulled back from the base,

`κ° : j^* ℱ ≃ j^* a^* 𝒞(g, s)`, `a : 𝔸¹_B ⟶ B`,

since over `𝔾_{m,B}` the deformation space is `V ×_B 𝔾_{m,B}` with `s̃ = s × 1`. -/
theorem nonempty_iso_leftDerivedUpperStar_puncturedLine_familyObject (hs : s ≫ g = 𝟙 B)
    [IsSeparated (Scheme.Hom.deformationSpaceProj g s)]
    [HasCompactification (Scheme.Hom.deformationSpaceProj g s)]
    [HasInvertibleExponent Λ s.ker.deformationSpace] :
    Nonempty ((L(((Scheme.Hom.puncturedLine B).ι)^*[ModuleCat.{u + 1} Λ])).obj
        (sectionInvariant Λ (Scheme.Hom.deformationSpaceProj g s) s.deformationSpaceSection) ≅
      (L(((Scheme.Hom.puncturedLine B).ι)^*[ModuleCat.{u + 1} Λ])).obj
        ((L((𝔸(ULift.{u} (Fin 1); B) ↘ B)^*[ModuleCat.{u + 1} Λ])).obj
          (sectionInvariant Λ g s))) := by
  have := Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj d g s hs
  set j := (Scheme.Hom.puncturedLine B).ι
  have PG := Scheme.Hom.isPullback_deformationSpaceGeneric g s
  have hm : (j ≫ s.deformationSpaceSection) ≫ Scheme.Hom.deformationSpaceProj g s = 𝟙 _ ≫ j := by
    rw [Category.assoc, Scheme.Hom.deformationSpaceSection_deformationSpaceProj hs,
      Category.comp_id, Category.id_comp]
  set m := PG.lift (j ≫ s.deformationSpaceSection) (𝟙 _) hm
  have hm₁ : m ≫ Scheme.Hom.deformationSpaceGeneric g s = j ≫ s.deformationSpaceSection :=
    PG.lift_fst _ _ _
  have hm₂ : m ≫ pullback.fst _ _ = j ≫ (𝔸(ULift.{u} (Fin 1); B) ↘ B) ≫ s := by
    rw [← Scheme.Hom.deformationSpaceGeneric_toBase g s, reassoc_of% hm₁,
      Scheme.Hom.deformationSpaceSection_toBase]
  obtain ⟨e₁⟩ := nonempty_iso_leftDerivedUpperStar_dualizingComplex Λ (d := d)
    (Scheme.Hom.deformationSpaceProj g s) PG
  obtain ⟨e₂⟩ := nonempty_iso_leftDerivedUpperStar_dualizingComplex Λ (d := d) g
    (IsPullback.of_hasPullback g (j ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B))
  exact ⟨((leftDerivedUpperStarComp _ j s.deformationSpaceSection).app _).symm ≪≫
    (leftDerivedUpperStarComp _ m (Scheme.Hom.deformationSpaceGeneric g s) _ hm₁.symm).app _ ≪≫
    (L((m)^*[ModuleCat.{u + 1} Λ])).mapIso (e₁ ≪≫ e₂.symm) ≪≫
    ((leftDerivedUpperStarComp _ m (pullback.fst _ _) _ rfl).app _).symm ≪≫
    (leftDerivedUpperStarComp _ (j ≫ 𝔸(ULift.{u} (Fin 1); B) ↘ B) s _ hm₂).app _ ≪≫
    (leftDerivedUpperStarComp _ j (𝔸(ULift.{u} (Fin 1); B) ↘ B)).app _⟩

end Construction

end Etale

end AlgebraicGeometry
