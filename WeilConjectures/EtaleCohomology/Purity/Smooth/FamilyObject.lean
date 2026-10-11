/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace.AffineSpace
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
- `AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_puncturedLine_familyObject`
- `AlgebraicGeometry.Etale.nonempty_iso_familyObject_standardPair`
- `AlgebraicGeometry.Etale.nonempty_iso_familyObject_standardPair_twistShift`
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
section StandardPair

variable (n : Type u) (B : Scheme.{u}) {d : ℕ} [IsSeparated (𝔸(n; B) ↘ B)]
  [SmoothOfRelativeDimension d (𝔸(n; B) ↘ B)] [HasCompactification (𝔸(n; B) ↘ B)]
  [HasInvertibleExponent Λ 𝔸(n; B)]

include d in
/-- Blueprint `sk-lem-geometry` (4), the family object of the standard pair: for the zero section
`0` of `𝔸^n_B ⟶ B`, the deformation space is `𝔸^n_{𝔸¹_B}`
(`AlgebraicGeometry.Scheme.Hom.isIso_deformationSpaceToAffineSpace`), so the family object is
pulled back from the base,

`ℱ ≃ a^* (0^* ω_{𝔸^n_B / B})`, `a : 𝔸¹_B ⟶ B`. -/
theorem nonempty_iso_familyObject_standardPair
    [HasCompactification
      (Scheme.Hom.deformationSpaceProj (𝔸(n; B) ↘ B) (AffineSpace.zeroSection n B))] :
    Nonempty (sectionInvariant Λ
        (Scheme.Hom.deformationSpaceProj (𝔸(n; B) ↘ B) (AffineSpace.zeroSection n B))
        (AffineSpace.zeroSection n B).deformationSpaceSection ≅
      (L((𝔸(ULift.{u} (Fin 1); B) ↘ B)^*[ModuleCat.{u + 1} Λ])).obj
        (sectionInvariant Λ (𝔸(n; B) ↘ B) (AffineSpace.zeroSection n B))) := by
  set Φ := Scheme.Hom.deformationSpaceToAffineSpace n B
  set a := 𝔸(ULift.{u} (Fin 1); B) ↘ B
  have sq : IsPullback (Φ ≫ AffineSpace.map n a)
      (Scheme.Hom.deformationSpaceProj (𝔸(n; B) ↘ B) (AffineSpace.zeroSection n B))
      (𝔸(n; B) ↘ B) a := by
    have := (IsPullback.of_horiz_isIso (g := 𝟙 _)
      ⟨(Scheme.Hom.deformationSpaceToAffineSpace_over n B).trans
        (Category.comp_id _).symm⟩).paste_horiz (AffineSpace.isPullback_map (n := n) a)
    simpa using this
  obtain ⟨e⟩ := nonempty_iso_leftDerivedUpperStar_dualizingComplex Λ (d := d) (𝔸(n; B) ↘ B) sq
  have hm : (AffineSpace.zeroSection n B).deformationSpaceSection ≫ Φ ≫ AffineSpace.map n a =
      a ≫ AffineSpace.zeroSection n B := by
    rw [reassoc_of% Scheme.Hom.deformationSpaceSection_comp_deformationSpaceToAffineSpace,
      AffineSpace.zeroSection_comp_map]
  exact ⟨(L(((AffineSpace.zeroSection n B).deformationSpaceSection)^*[ModuleCat.{u + 1} Λ])).mapIso
      e.symm ≪≫
    ((leftDerivedUpperStarComp _ _ (Φ ≫ AffineSpace.map n a)).app _).symm ≪≫
    (leftDerivedUpperStarComp _ a (AffineSpace.zeroSection n B) _ hm).app _⟩

end StandardPair
/-- Blueprint `sk-lem-geometry` (4), the family object of the standard pair, made explicit: for
the zero section of `𝔸^c_B ⟶ B` over a separated scheme of finite type over a field, the
family object is the constant Tate twist,

`ℱ ≃ a^* (0^* ω_{𝔸^c_B / B}) ≃ a^* Λ_B(c)[2c] ≃ Λ_{𝔸¹_B}(c)[2c]`,

where `0^* ω = Λ(c)[2c]` is vector-bundle purity for the trivial bundle
(`AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_affineSpace`). -/
theorem nonempty_iso_familyObject_standardPair_twistShift [HasTateTwist.IsNormalized Λ]
    {k : Type u} [Field k] (c : ℕ) (B : Scheme.{u}) (aB : B ⟶ Spec (.of k)) [IsSeparated aB]
    [LocallyOfFiniteType aB] [HasInvertibleExponent Λ B]
    [SmoothOfRelativeDimension c (𝔸(ULift.{u} (Fin c); B) ↘ B)]
    [HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin c); B)]
    [HasCompactification (Scheme.Hom.deformationSpaceProj (𝔸(ULift.{u} (Fin c); B) ↘ B)
      (AffineSpace.zeroSection (ULift.{u} (Fin c)) B))] :
    Nonempty (sectionInvariant Λ
        (Scheme.Hom.deformationSpaceProj (𝔸(ULift.{u} (Fin c); B) ↘ B)
          (AffineSpace.zeroSection (ULift.{u} (Fin c)) B))
        (AffineSpace.zeroSection (ULift.{u} (Fin c)) B).deformationSpaceSection ≅
      (twistShift Λ 𝔸(ULift.{u} (Fin 1); B) c).obj
        (constantComplex Λ 𝔸(ULift.{u} (Fin 1); B))) := by
  obtain ⟨e₁⟩ := nonempty_iso_familyObject_standardPair Λ (ULift.{u} (Fin c)) B (d := c)
  obtain ⟨e₂⟩ := nonempty_iso_sectionInvariant_affineSpace Λ c B aB
  exact ⟨e₁ ≪≫ (L((𝔸(ULift.{u} (Fin 1); B) ↘ B)^*[ModuleCat.{u + 1} Λ])).mapIso
      (e₂ ≪≫ twistShiftConstantComplexIso Λ B c) ≪≫
    leftDerivedUpperStarTateShiftIso Λ _ c ≪≫ (twistShiftConstantComplexIso Λ _ c).symm⟩

end Etale

end AlgebraicGeometry
