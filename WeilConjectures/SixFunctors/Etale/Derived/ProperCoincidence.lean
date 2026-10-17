/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionRefinement
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompCoherence

/-!
# Proper coincidence: `Rf_! ≅ Rf_*` canonically

For a compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`, the *forget-supports* map
`ψ_c : Rf_!(c) = Rg_* D(i_!) ⟶ Rg_* Ri_* ⟶ Rf_*`. For a refinement of compactifications the
comparison of lower shrieks intertwines the forget-supports maps.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f} (r : c.Refinement d)

/-- Associativity of the composition maps of derived pushforwards along a refinement. -/
lemma rightDerivedLowerStarCompHom_refinement_assoc
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (rightDerivedLowerStarCompHom A r.hom d.g c.g r.hom_g.symm).app (R((c.i)_*[A]).obj M) ≫
        (rightDerivedLowerStarCompHom A c.i c.g f c.comm).app M =
      R((d.g)_*[A]).map ((rightDerivedLowerStarCompHom A c.i r.hom d.i r.i_hom.symm).app M) ≫
        (rightDerivedLowerStarCompHom A d.i d.g f d.comm).app M := by
  have h := leftDerivedUpperStarComp_assoc' A c.i r.hom d.g d.i c.g f r.i_hom.symm
    r.hom_g.symm d.comm
  have e₁ := conjugateEquiv_whiskerRight
    ((derivedUpperStarLowerStarAdjunction A d.g).comp (derivedUpperStarLowerStarAdjunction A r.hom))
    (derivedUpperStarLowerStarAdjunction A c.g)
    (derivedUpperStarLowerStarAdjunction A c.i) (leftDerivedUpperStarComp A r.hom d.g c.g
      r.hom_g.symm).hom
  have e₂ := conjugateEquiv_whiskerLeft
    ((derivedUpperStarLowerStarAdjunction A r.hom).comp (derivedUpperStarLowerStarAdjunction A c.i))
    (derivedUpperStarLowerStarAdjunction A d.i)
    (derivedUpperStarLowerStarAdjunction A d.g) (leftDerivedUpperStarComp A c.i r.hom d.i
      r.i_hom.symm).hom
  have key : (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft R((c.i)_*[A])
        (rightDerivedLowerStarCompHom A r.hom d.g c.g r.hom_g.symm) ≫
        rightDerivedLowerStarCompHom A c.i c.g f c.comm =
      Functor.whiskerRight (rightDerivedLowerStarCompHom A c.i r.hom d.i r.i_hom.symm)
        R((d.g)_*[A]) ≫ rightDerivedLowerStarCompHom A d.i d.g f d.comm := by
    simp only [rightDerivedLowerStarCompHom]
    rw [← e₁, ← e₂, conjugateEquiv_comp, conjugateEquiv_comp, ← conjugateEquiv_associator_hom,
      conjugateEquiv_comp]
    congr 1
    rw [h]
    ext K
    simp
  have := NatTrans.congr_app key M
  simpa using this

variable [HasSmallSiteSheafify A]

/-- On sheaves: the base change `(c.i)_! ⟶ (d.i)_! ⋙ q^*` of a refinement is compatible with the
units of `(c.i)_! ⊣ (c.i)^*` and `(d.i)_! ⊣ (d.i)^*` through `(d.i)^* ≅ q^* ⋙ (c.i)^*`. -/
lemma unit_comp_map_refinementOpenImmersionLowerShriekBaseChange
    (M : Sheaf X.smallEtaleTopology A) :
    (openImmersionLowerShriekUpperStarAdjunction A c.i).unit.app M ≫
        ((c.i)^*[A]).map ((r.openImmersionLowerShriekBaseChange A).app M) =
      (openImmersionLowerShriekUpperStarAdjunction A d.i).unit.app M ≫
        (upperStarComp A c.i r.hom d.i r.i_hom.symm).hom.app (((d.i)_!open[A]).obj M) := by
  have h := unit_conjugateEquiv ((openImmersionLowerShriekUpperStarAdjunction A d.i).comp
    (upperStarLowerStarAdjunction A r.hom)) (openImmersionLowerShriekUpperStarAdjunction A c.i)
    (r.openImmersionLowerShriekBaseChange A) M
  have hc : conjugateEquiv ((openImmersionLowerShriekUpperStarAdjunction A d.i).comp
      (upperStarLowerStarAdjunction A r.hom)) (openImmersionLowerShriekUpperStarAdjunction A c.i)
      (r.openImmersionLowerShriekBaseChange A) = upperStarBaseChange A c.i r.hom d.i r.i_hom := by
    simp [Compactification.Refinement.openImmersionLowerShriekBaseChange,
      Etale.openImmersionLowerShriekBaseChange]
  rw [hc, Adjunction.comp_unit_app, upperStarBaseChange_app, Category.assoc] at h
  rw [← h]
  congr 1
  have hn := (upperStarComp A c.i r.hom d.i r.i_hom.symm).hom.naturality
    ((upperStarLowerStarAdjunction A r.hom).unit.app (((d.i)_!open[A]).obj M))
  simp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  rw [← Functor.map_comp]
  simp

/-- The derived form of `unit_comp_map_refinementOpenImmersionLowerShriekBaseChange`, for a
refinement whose square over `X` is cartesian. -/
lemma derivedUnit_comp_map_refinementLowerShriekBaseChangeDerivedIso
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction A c.i).unit.app M ≫
        D((c.i)^*[A]).map ((refinementLowerShriekBaseChangeDerivedIso A r hcart).hom.app M) =
      (derivedOpenImmersionLowerShriekUpperStarAdjunction A d.i).unit.app M ≫
        (Functor.mapDerivedCategoryNatIso (upperStarComp A c.i r.hom d.i r.i_hom.symm) ≪≫
          Functor.mapDerivedCategoryCompIso _ _).hom.app (D((d.i)_!open[A]).obj M) := by
  haveI := r.isIso_openImmersionLowerShriekBaseChange A hcart
  exact Adjunction.mapDerivedCategoryAdjunction_mate'
    (openImmersionLowerShriekUpperStarAdjunction A d.i)
    (openImmersionLowerShriekUpperStarAdjunction A c.i)
    (upperStarComp A c.i r.hom d.i r.i_hom.symm) (asIso (r.openImmersionLowerShriekBaseChange A))
    (fun K ↦ unit_comp_map_refinementOpenImmersionLowerShriekBaseChange A r K) M

/-- The transpose of the comparison `D(j_!) ⟶ Rj_*` under `D(j^*) ⊣ Rj_*` is the inverse of the
unit of `D(j_!) ⊣ D(j^*)`. -/
@[reassoc]
lemma map_derivedOpenImmersionLowerShriekToLowerStar_app_comp_counit {U Z : Scheme.{u}}
    (j : U ⟶ Z) [IsOpenImmersion j] (M : DerivedCategory (Sheaf U.smallEtaleTopology A)) :
    D((j)^*[A]).map ((derivedOpenImmersionLowerShriekToLowerStar A j).app M) ≫
        (mapDerivedUpperStarLowerStarAdjunction A j).counit.app M =
      inv ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit.app M) := by
  have hn := (mapDerivedUpperStarLowerStarAdjunction A j).counit.naturality
    (inv ((derivedOpenImmersionLowerShriekUpperStarAdjunction A j).unit.app M))
  simp only [Functor.comp_map, Functor.id_map] at hn
  simp only [derivedOpenImmersionLowerShriekToLowerStar, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Functor.whiskerRight_app,
    NatIso.isIso_inv_app, Category.id_comp, Functor.map_comp]
  rw [Category.assoc]
  erw [hn]
  rw [← Category.assoc]
  erw [Adjunction.left_triangle_components]
  rw [Category.id_comp]

/-- The composition map `Rq_* ⋙ R(c.i)_* ... `: conjugate, under the levelwise derived
adjunctions, of the composition isomorphism `D(k^*) ≅ D(q^*) ⋙ D(j^*)`. -/
noncomputable abbrev rightDerivedLowerStarCompHom' {T S R : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ R)
    (g₁₂ : T ⟶ R) (hg : g₁₂ = g₁ ≫ g₂) :
    R((g₁)_*[A]) ⋙ R((g₂)_*[A]) ⟶ R((g₁₂)_*[A]) :=
  conjugateEquiv ((mapDerivedUpperStarLowerStarAdjunction A g₂).comp
      (mapDerivedUpperStarLowerStarAdjunction A g₁)) (mapDerivedUpperStarLowerStarAdjunction A g₁₂)
    (Functor.mapDerivedCategoryNatIso (upperStarComp A g₁ g₂ g₁₂ hg) ≪≫
      Functor.mapDerivedCategoryCompIso _ _).hom

/-- **The comparison `D(j_!) ⟶ Rj_*` along a refinement**: for a refinement `r` of
compactifications with cartesian square over `X` and `q = r.hom`, the comparison for `d.i` is
the unit of `D(q^*) ⊣ Rq_*`, followed by `Rq_*` of the inverse base change
`D(d.i)_! ⋙ D(q^*) ≅ D(c.i)_!` and of the comparison for `c.i`, and by the composition map
`R(c.i)_* ⋙ Rq_* ⟶ R(d.i)_*`. -/
lemma derivedOpenImmersionLowerShriekToLowerStar_app_eq_of_refinement
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (derivedOpenImmersionLowerShriekToLowerStar A d.i).app M =
      (mapDerivedUpperStarLowerStarAdjunction A r.hom).unit.app (D((d.i)_!open[A]).obj M) ≫
        R((r.hom)_*[A]).map ((refinementLowerShriekBaseChangeDerivedIso A r hcart).inv.app M ≫
          (derivedOpenImmersionLowerShriekToLowerStar A c.i).app M) ≫
        (rightDerivedLowerStarCompHom' A c.i r.hom d.i r.i_hom.symm).app M := by
  apply ((mapDerivedUpperStarLowerStarAdjunction A d.i).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  rw [map_derivedOpenImmersionLowerShriekToLowerStar_app_comp_counit, Functor.map_comp,
    Functor.map_comp, Category.assoc, Category.assoc, conjugateEquiv_counit,
    Adjunction.comp_counit_app]
  set ϕ := Functor.mapDerivedCategoryNatIso (upperStarComp A c.i r.hom d.i r.i_hom.symm) ≪≫
    (r.hom)^*[A].mapDerivedCategoryCompIso (c.i)^*[A]
  set y := (refinementLowerShriekBaseChangeDerivedIso A r hcart).inv.app M ≫
    (derivedOpenImmersionLowerShriekToLowerStar A c.i).app M
  have h1 := ϕ.hom.naturality (R((r.hom)_*[A]).map y)
  have h2 := ϕ.hom.naturality ((mapDerivedUpperStarLowerStarAdjunction A r.hom).unit.app
    (D((d.i)_!open[A]).obj M))
  have h3 := (mapDerivedUpperStarLowerStarAdjunction A r.hom).counit.naturality y
  have h4 := (mapDerivedUpperStarLowerStarAdjunction A r.hom).left_triangle_components
    (D((d.i)_!open[A]).obj M)
  simp only [Functor.comp_map, Functor.id_map] at h1 h2 h3
  erw [reassoc_of% h1, reassoc_of% h2]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc, Category.assoc]
  erw [h3, reassoc_of% h4]
  simp only [y, Functor.map_comp, Category.assoc]
  rw [map_derivedOpenImmersionLowerShriekToLowerStar_app_comp_counit]
  have h6 := derivedUnit_comp_map_refinementLowerShriekBaseChangeDerivedIso A r hcart M
  rw [← cancel_epi ((derivedOpenImmersionLowerShriekUpperStarAdjunction A d.i).unit.app M),
    IsIso.hom_inv_id]
  erw [← reassoc_of% h6]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, IsIso.hom_inv_id]
  rfl

omit [HasSmallSiteSheafify A] in
lemma rightDerivedLowerStarCompHom_eq' {T S R : Scheme.{u}} (g₁ : T ⟶ S) (g₂ : S ⟶ R)
    (g₁₂ : T ⟶ R) (hg : g₁₂ = g₁ ≫ g₂) :
    rightDerivedLowerStarCompHom A g₁ g₂ g₁₂ hg = rightDerivedLowerStarCompHom' A g₁ g₂ g₁₂ hg :=
  conjugateEquiv_leftDerivedUpperStarComp_hom A g₁ g₂ g₁₂ hg

/-- The *forget-supports* map `ψ_c : Rf_!(c) = Rg_* D(i_!) ⟶ Rg_* Ri_* ⟶ Rf_*` of a
compactification `c = (X ⟶[i] Z ⟶[g] Y)` of `f`: `Rg_*` of the comparison `D(i_!) ⟶ Ri_*`,
followed by the composition map `Rg_* Ri_* ⟶ Rf_*`. -/
noncomputable def rightDerivedLowerShriekOfCompactificationToLowerStar (c : Compactification f) :
    Rf_!(c)[A] ⟶ R((f)_*[A]) :=
  Functor.whiskerRight (derivedOpenImmersionLowerShriekToLowerStar A c.i) R((c.g)_*[A]) ≫
    rightDerivedLowerStarCompHom A c.i c.g f c.comm

/-- **The forget-supports maps are compatible with refinements**: for a refinement `r` of
compactifications of `f` with cartesian square over `X`, the comparison `Rf_!(d) ⟶ Rf_!(c)`
followed by `ψ_c` is `ψ_d`. -/
theorem rightDerivedLowerShriekOfCompactificationComparison_comp_toLowerStar
    (hcart : IsPullback c.i (𝟙 X) r.hom d.i) :
    rightDerivedLowerShriekOfCompactificationComparison A r hcart ≫
        rightDerivedLowerShriekOfCompactificationToLowerStar A c =
      rightDerivedLowerShriekOfCompactificationToLowerStar A d := by
  ext M
  have hQ := derivedOpenImmersionLowerShriekToLowerStar_app_eq_of_refinement A r hcart M
  have hA := rightDerivedLowerStarCompHom_refinement_assoc A r M
  have hn := (rightDerivedLowerStarCompHom' A r.hom d.g c.g r.hom_g.symm).naturality
    ((derivedOpenImmersionLowerShriekToLowerStar A c.i).app M)
  simp only [rightDerivedLowerStarCompHom_eq'] at hA
  simp only [rightDerivedLowerShriekOfCompactificationToLowerStar,
    rightDerivedLowerShriekOfCompactificationComparison, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc,
    rightDerivedFunctorCompIso'_refinementLowerStarComp_hom, rightDerivedLowerStarCompHom_eq']
  erw [← reassoc_of% hn, hA, hQ]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]

omit [HasSmallSiteSheafify A] in
/-- For a proper `f`, the forget-supports map `ψ_c : Rf_!(c) ⟶ Rf_*` of every compactification
`c` is an isomorphism: the open immersion `c.i` is then also closed. -/
instance isIso_rightDerivedLowerShriekOfCompactificationToLowerStar [IsProper f]
    (c : Compactification f) : IsIso (rightDerivedLowerShriekOfCompactificationToLowerStar A c) := by
  have := c.isClosedImmersion_openImmersion ‹_›
  unfold rightDerivedLowerShriekOfCompactificationToLowerStar
  infer_instance

section Torsion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- **The forget-supports maps do not depend on the compactification**: for two compactifications
`c`, `d` of a quasi-compact `f`, the identification `Rf_!(c) ≅ Rf_!(d)` carries `ψ_d` to `ψ_c`. -/
theorem rightDerivedLowerShriekOfCompactificationIso_hom_comp_toLowerStar [QuasiCompact f]
    (c d : Compactification f) :
    (rightDerivedLowerShriekOfCompactificationIso Λ c d).hom ≫
        rightDerivedLowerShriekOfCompactificationToLowerStar (ModuleCat.{u + 1} Λ) d =
      rightDerivedLowerShriekOfCompactificationToLowerStar (ModuleCat.{u + 1} Λ) c := by
  have h₂ : inv (rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} Λ)
      (Compactification.infSnd c d) (Compactification.isPullback_infSnd c d)) ≫
        rightDerivedLowerShriekOfCompactificationToLowerStar (ModuleCat.{u + 1} Λ) d =
      rightDerivedLowerShriekOfCompactificationToLowerStar (ModuleCat.{u + 1} Λ)
        (Compactification.inf c d) := by
    rw [IsIso.inv_comp_eq, rightDerivedLowerShriekOfCompactificationComparison_comp_toLowerStar]
  simp only [rightDerivedLowerShriekOfCompactificationIso, Iso.trans_hom, asIso_hom, Iso.symm_hom,
    asIso_inv, Category.assoc, h₂]
  exact rightDerivedLowerShriekOfCompactificationComparison_comp_toLowerStar _ _ _

/-- Blueprint `sk-prop-sf-comp-proper`: Proper coincidence

**Proper coincidence, canonically.** Let `f : X ⟶ Y` be proper and `Λ` finite. Then `(𝟙 X, f)`
is a compactification of `f` (`AlgebraicGeometry.Compactification.ofIsProper`), and for every
compactification `c = (i, g)` of `f` the forget-supports map
`ψ_c : Rf_!(c) = Rg_* D(i_!) ⟶ Rg_* Ri_* ⟶ Rf_*` is an isomorphism; for `c = (𝟙 X, f)` it is the
identification `Rf_! = Rf_* ∘ 𝟙_! ≅ Rf_*`. The identification is independent of the
compactification: under the comparison `Rf_!(c) ≅ Rf_!(d)` of any two compactifications,
`ψ_d` corresponds to `ψ_c`; in particular, for `R(f)_!`, defined with the chosen
compactification, `ψ_c` is `ψ` of the chosen one after `Rf_!(c) ≅ R(f)_!`. -/
theorem isIso_rightDerivedLowerShriekOfCompactificationToLowerStar_and_independent [IsProper f]
    [HasCompactification f] :
    (∀ c : Compactification f,
      IsIso (rightDerivedLowerShriekOfCompactificationToLowerStar (ModuleCat.{u + 1} Λ) c)) ∧
    (∀ c d : Compactification f,
      (rightDerivedLowerShriekOfCompactificationIso Λ c d).hom ≫
          rightDerivedLowerShriekOfCompactificationToLowerStar (ModuleCat.{u + 1} Λ) d =
        rightDerivedLowerShriekOfCompactificationToLowerStar (ModuleCat.{u + 1} Λ) c) ∧
    (rightDerivedLowerShriekIso Λ (Compactification.ofIsProper f)).hom ≫
        rightDerivedLowerShriekOfCompactificationToLowerStar (ModuleCat.{u + 1} Λ)
          (HasCompactification.compactification f) =
      rightDerivedLowerShriekOfCompactificationToLowerStar (ModuleCat.{u + 1} Λ)
        (Compactification.ofIsProper f) :=
  ⟨fun c ↦ inferInstance, fun c d ↦
    rightDerivedLowerShriekOfCompactificationIso_hom_comp_toLowerStar Λ c d,
    rightDerivedLowerShriekOfCompactificationIso_hom_comp_toLowerStar Λ _ _⟩

end Torsion

end Etale

end AlgebraicGeometry
