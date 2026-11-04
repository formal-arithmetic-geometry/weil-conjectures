/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ZeroSectionPurity
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLineNormalization
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerOrientation
public import WeilConjectures.EtaleCohomology.TateTwist.Normalized
public import WeilConjectures.EtaleCohomology.Purity.Smooth.AffineLine

/-! # The affine and punctured line over an arbitrary base, étale

For every scheme `B` on which the exponent of a finite coefficient ring `Λ` is invertible
(no finiteness assumption on `B`): the unit of `p : 𝔸¹_B ⟶ B` at `Λ_B` is an isomorphism, and
for `π : 𝔾_{m,B} ⟶ B` the unit is an isomorphism on `H⁰` (for `Λ` and `Λ(1)`), the Kummer
class of the coordinate generates `R¹π_* Λ(1)`, and `R^mπ_* Λ(1) = 0` for `m ≥ 2`.
These are deduced from homotopy invariance of the affine line over an arbitrary base and
relative purity for the zero section, by reading the localization triangle backwards
(blueprint: lem-pur-relative-kummer-arbitrary-base-maps, Steps 1 and 2).
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated MonoidalCategory

open scoped CategoryTheory.Functor

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- Converse of `DerivedCategory.isIso_shiftedHomComp_of_distTriang`: let `A ⟶ P ⟶ Q ⟶ A[1]`
be a distinguished triangle in `D(C)` and `κ : E ⟶ Q[1]`, where `E` and `P` have cohomology
only in degree `0`. If the composite `E ⟶ Q[1] ⟶ A[2]` is an isomorphism, then
`H⁰(P) ⟶ H⁰(Q)` is an isomorphism, `Q` has cohomology only in degrees `0` and `1`, and `κ`
induces an isomorphism `H⁰(E) ≅ H¹(Q)`. -/
theorem homology_props_of_isIso_shiftedHomComp (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) {E : DerivedCategory C} (κ : E ⟶ T.obj₃⟦(1 : ℤ)⟧)
    (hE : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor C n).obj E))
    (hP : ∀ n : ℤ, n ≠ 0 → IsZero ((homologyFunctor C n).obj T.obj₂))
    (hiso : IsIso (ShiftedHom.comp κ T.mor₃ (by norm_num : (1 : ℤ) + 1 = 2))) :
    IsIso ((homologyFunctor C 0).map T.mor₂) ∧
      (∀ n : ℤ, n ≠ 0 → n ≠ 1 → IsZero ((homologyFunctor C n).obj T.obj₃)) ∧
      IsIso ((homologyFunctor C 0).shiftMap κ 0 1 (by simp)) := by
  -- the supported term has cohomology only in degree `2`
  have hA : ∀ n : ℤ, n ≠ 2 → IsZero ((homologyFunctor C n).obj T.obj₁) := fun n hn ↦
    (hE (n - 2) (by lia)).of_iso
      ((((homologyFunctor C 0).shiftIso (2 : ℤ) (n - 2) n (by omega)).app T.obj₁).symm ≪≫
        (homologyFunctor C (n - 2)).mapIso
          (@asIso _ _ _ _ _ hiso).symm)
  have hQ : ∀ n : ℤ, n ≠ 0 → n ≠ 1 → IsZero ((homologyFunctor C n).obj T.obj₃) :=
    fun n h0 h1 ↦ (HomologySequence.exact₃ T hT n (n + 1)).isZero_of_both_zeros
      ((hP n h0).eq_of_src _ _) ((hA (n + 1) (by lia)).eq_of_tgt _ _)
  have h₀ : IsIso ((homologyFunctor C 0).map T.mor₂) := by
    have : Mono ((homologyFunctor C 0).map T.mor₂) :=
      (HomologySequence.mono_homologyMap_mor₂_iff T hT 0).2
        ((hA 0 (by norm_num)).eq_of_src _ _)
    have : Epi ((homologyFunctor C 0).map T.mor₂) :=
      (HomologySequence.epi_homologyMap_mor₂_iff T hT 0 1).2
        ((hA 1 (by norm_num)).eq_of_tgt _ _)
    exact isIso_of_mono_of_epi _
  have hδ : IsIso (HomologySequence.δ T 1 2) := by
    have hm : Mono (HomologySequence.δ T 1 2) :=
      (HomologySequence.exact₃ T hT 1 2).mono_g ((hP 1 one_ne_zero).eq_of_src _ _)
    have he : Epi (HomologySequence.δ T 1 2) :=
      (HomologySequence.exact₁ T hT 1 2).epi_f ((hP 2 two_ne_zero).eq_of_tgt _ _)
    exact isIso_of_mono_of_epi _
  refine ⟨h₀, hQ, ?_⟩
  have h := (homologyFunctor C 0).shiftMap_shiftedHomComp κ T.mor₃
    (by norm_num : (1 : ℤ) + 1 = 2) 0 1 2 (by norm_num) (by norm_num)
  have : IsIso ((homologyFunctor C 0).shiftMap
      (ShiftedHom.comp κ T.mor₃ (by norm_num : (1 : ℤ) + 1 = 2)) 0 2 (by norm_num)) := by
    rw [Functor.shiftMap]
    infer_instance
  rw [h] at this
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ hδ this

end DerivedCategory

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Homotopy invariance of the affine line over an arbitrary base for the constant
coefficients: for every scheme `S` on which the exponent of `Λ` is invertible, the unit
`Λ_S ⟶ Rp_* Lp^* Λ_S` of the projection `p : 𝔸¹_S ⟶ S` is an isomorphism. The proof is that of
`AlgebraicGeometry.Etale.isIso_unit_tateObject_affineLine_of_strictlyHenselian`. -/
theorem isIso_unit_constantComplex_affineLine_of_hasInvertibleExponent (S : Scheme.{u})
    [HasInvertibleExponent Λ S] :
    IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (𝔸(ULift.{u} (Fin 1); S) ↘ S)).unit.app (constantComplex Λ S)) := by
  have : NeZero (ringChar Λ) := neZero_ringChar_of_finite Λ
  let L : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ) := 𝟙_ _
  have hL : IsLocallyConstantSheaf L :=
    (isFiniteLocallyConstantSheaf_constantSheaf (𝟙_ (ModuleCat.{u + 1} Λ))).toIsLocallyConstantSheaf
  let eL := constantComplexIsoSingleFunctor Λ S
  refine isIso_of_isIso_leftDerivedUpperStar_algClosurePoint_map Λ _ fun s ↦ ?_
  rw [_root_.DerivedCategory.isIso_iff]
  intro n
  have : HasInvertibleExponent Λ (Spec (.of (AlgebraicClosure (S.residueField s)))) :=
    .of_hom (S.algClosurePoint s)
  have : HasInvertibleExponent Λ 𝔸(ULift.{u} (Fin 1); S) := .of_hom (𝔸(ULift.{u} (Fin 1); S) ↘ S)
  let sq := AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) (S.algClosurePoint s)
  have hBC : IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
      ((L((𝔸(ULift.{u} (Fin 1); S) ↘ S)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ S))) := by
    refine (NatTrans.isIso_app_iff_of_iso _
      ((L((𝔸(ULift.{u} (Fin 1); S) ↘ S)^*[ModuleCat.{u + 1} Λ])).mapIso eL ≪≫
        (singleFunctorCompLeftDerivedUpperStarIso _ (𝔸(ULift.{u} (Fin 1); S) ↘ S)).app L)).2 ?_
    refine (isIso_derivedBaseChangeMap_app_ι_obj_iff (ModuleCat.{u + 1} Λ) sq.toCommSq
      ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((𝔸(ULift.{u} (Fin 1); S) ↘ S)^*[ModuleCat.{u + 1} Λ].obj L))).2 ?_
    rw [← baseChange_eq_derivedBaseChangeMapPlus]
    exact (isIso_baseChange_app_singleFunctor_obj_iff Λ sq _).2 fun q ↦
      isIso_baseChangeHomologyMap_affineLine_upperStar Λ sq L q
  have := isIso_unit_constantComplex_affineLine Λ
    (𝟙 (Spec (.of (AlgebraicClosure (S.residueField s)))))
  exact isIso_homology_map_leftDerivedUpperStar_unit_app Λ sq.toCommSq _
    (leftDerivedUpperStarConstantComplexIso Λ (S.algClosurePoint s)) n hBC inferInstance

section Kummer

variable [NeZero (ringChar Λ)]

attribute [local instance] HasInvertibleExponent.opens

/-- **The punctured line over an arbitrary base.** For every scheme `B` on which the exponent
of `Λ` is invertible, with `p : 𝔸¹_B ⟶ B`, `j : 𝔾_{m,B} ⟶ 𝔸¹_B` and `π = p ∘ j`:
the restriction `R⁰p_* Λ(1) ⟶ R⁰π_* Λ(1)` is an isomorphism, the Kummer class induces an
isomorphism `Λ_B ≅ R¹π_* Λ(1)`, and `R^mπ_* Λ(1) = 0` for `m ≠ 0, 1`. This is the converse of
`AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundary_coord_of_affineLine`, deduced
from relative purity for the zero section
(`AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundary_coord_of_hasInvertibleExponent`)
and homotopy invariance of the affine line
(`AlgebraicGeometry.Etale.isIso_unit_tateObject_affineLine_of_strictlyHenselian`). -/
theorem affineLine_kummer_clauses_of_hasInvertibleExponent (B : Scheme.{u})
    [HasInvertibleExponent Λ B] :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          ((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι)).unit.app
            (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1)))) ∧
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).shiftMap
      (kummerClassAffineLineDirectImage Λ B) 0 1 (by norm_num)) ∧
    ∀ n : ℤ, n ≠ 0 → n ≠ 1 → IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R((𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).obj
        ((R(((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι)_*[
            ModuleCat.{u + 1} Λ])).obj
          ((L(((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι)^*[
            ModuleCat.{u + 1} Λ])).obj (tateObject Λ 𝔸(ULift.{u} (Fin 1); B) 1))))) := by
  let t := AffineSpace.coord B (ULift.up.{u} (0 : Fin 1))
  let X := 𝔸(ULift.{u} (Fin 1); B)
  let p := X ↘ B
  let i := X.zeroLocusSubschemeι {t}
  let Rp := R((p)_*[ModuleCat.{u + 1} Λ])
  have : IsIso (i ≫ p) :=
    inferInstanceAs (IsIso (AffineSpace.zeroSectionIsoZeroLocusSubscheme (ULift.{u} (Fin 1)) B
      (s := {t}) Set.range_unique).inv)
  have : HasInvertibleExponent Λ X := .of_hom p
  -- the localization triangle of `(V(t), 𝔾_m)`, pushed forward to `B`
  let T₁ := supportedLocalizationTriangle Λ i (X.basicOpen t).ι
    (tateObject Λ X 1) (supportedLocalizationBoundary Λ _ _
      (range_zeroLocusSubschemeι_singleton t) (tateObject Λ X 1))
  have hT₁ : T₁ ∈ distTriang _ := supportedLocalizationTriangle_mem_distTriang _ _ _ _ _
  let T₂ := Rp.mapTriangle.obj T₁
  have hT₂ : T₂ ∈ distTriang _ := Rp.map_distinguished _ hT₁
  have hE : ∀ n : ℤ, n ≠ 0 → IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      (constantComplex Λ B)) := fun n hn ↦
    (HomologicalComplex.isZero_single_obj_homology _ _ _ _ hn).of_iso
      ((_root_.DerivedCategory.homologyFunctor _ n).mapIso
        (constantComplexIsoSingleFunctor Λ B ≪≫
          (_root_.DerivedCategory.singleFunctorIsoCompQ _ 0).app _) ≪≫
        (_root_.DerivedCategory.homologyFunctorFactors _ n).app _)
  -- `Rp_* Λ(1)` is concentrated in degree zero, by homotopy invariance
  have ha : ∀ n : ℤ, n ≠ 0 →
      IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj T₂.obj₂) := by
    obtain ⟨LT, -, -, ⟨eTY⟩⟩ := HasTateTwist.exists_isLocallyConstantSheaf_twistObject
      (Λ := Λ) B 1
    have := isIso_unit_tateObject_affineLine_of_strictlyHenselian Λ B
    intro n hn
    exact (_root_.DerivedCategory.isZero_homologyFunctor_obj_of_iso_singleFunctor eTY hn).of_iso
      ((_root_.DerivedCategory.homologyFunctor _ n).mapIso
        ((Rp.mapIso (leftDerivedUpperStarTateObjectIso p 1)).symm ≪≫
          (asIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app
            (tateObject Λ B 1))).symm))
  -- relative purity: `Rp_*` of `∂κ(t)` is an isomorphism
  have hpur := isIso_supportedClassMap_kummerBoundary_coord_of_hasInvertibleExponent Λ B
  let u := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app
      (constantComplex Λ B) ≫ Rp.map (leftDerivedUpperStarConstantComplexIso Λ p).hom
  have hkey : u ≫ Rp.map (kummerBoundary Λ t) =
      ShiftedHom.comp (kummerClassAffineLineDirectImage Λ B)
        (ShiftedHom.map (supportedLocalizationBoundary Λ _ _
          (range_zeroLocusSubschemeι_singleton t) (tateObject Λ X 1)) Rp) (by norm_num) ≫
        (Rp.commShiftIso (2 : ℤ)).inv.app _ := by
    have h1 : Rp.map (kummerBoundary Λ t) = ShiftedHom.map (kummerBoundary Λ t) Rp ≫
        (Rp.commShiftIso (2 : ℤ)).inv.app _ := by
      simp [ShiftedHom.map]
    rw [h1, kummerBoundary_eq_comp, ShiftedHom.map_comp]
    simp only [ShiftedHom.comp, kummerClassAffineLineDirectImage, u, t, X, p, Rp,
      Category.assoc]
  have hγ := eq_comp_rightDerivedLowerShriek_map_supportedClassMap Λ i
    (shiftSupportedClass Λ i 2 (kummerBoundary Λ t))
  have hu := isIso_unit_comp_rightDerivedLowerStar_map_unit Λ i p
  rw [Functor.map_comp Rp (leftDerivedUpperStarConstantComplexIso Λ p).hom,
    ← Category.assoc] at hu
  have h3 : IsIso (u ≫ Rp.map (shiftSupportedClass Λ i 2 (kummerBoundary Λ t))) := by
    rw [hγ, Functor.map_comp, ← Category.assoc]
    infer_instance
  rw [shiftSupportedClass, Functor.map_comp, ← Category.assoc, hkey] at h3
  rw [isIso_comp_right_iff, isIso_comp_right_iff] at h3
  have h := DerivedCategory.homology_props_of_isIso_shiftedHomComp T₂ hT₂
    (kummerClassAffineLineDirectImage Λ B) hE ha h3
  exact ⟨h.1, h.2.2, h.2.1⟩

omit [Finite Λ] [NeZero (ringChar Λ)] in
/-- For `π = j ≫ p`, `H⁰` of the unit of `π` at `M` is an isomorphism if the unit of `p` at
`M` is an isomorphism and `H⁰` of `Rp_*` of the unit of `j` at `Lp^* M` is. -/
lemma isIso_homology_zero_unit_comp_of_isIso {X Y G : Scheme.{u}} (p : X ⟶ Y) (j : G ⟶ X)
    (M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hp : IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app M))
    (hj : IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((R((p)_*[ModuleCat.{u + 1} Λ])).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app
          ((L((p)^*[ModuleCat.{u + 1} Λ])).obj M))))) :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (j ≫ p)).unit.app M)) := by
  have hc : IsIso ((rightDerivedLowerStarCompHom (ModuleCat.{u + 1} Λ) j p (j ≫ p) rfl).app
      ((L((j)^*[ModuleCat.{u + 1} Λ])).obj ((L((p)^*[ModuleCat.{u + 1} Λ])).obj M))) := by
    rw [← rightDerivedLowerStarComp_hom_comp_congr_hom]
    infer_instance
  have hu := congrArg (_root_.DerivedCategory.homologyFunctor _ 0).map
    (unit_comp_rightDerivedLowerStar_map_unit Λ p j M)
  simp only [Functor.map_comp] at hu
  have h1 : IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (j ≫ p)).unit.app M) ≫
      (_root_.DerivedCategory.homologyFunctor _ 0).map ((R((j ≫ p)_*[ModuleCat.{u + 1} Λ])).map
        ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) j p (j ≫ p) rfl).hom.app M))) := by
    rw [← hu]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((_root_.DerivedCategory.homologyFunctor _ 0).map
    ((R((j ≫ p)_*[ModuleCat.{u + 1} Λ])).map
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) j p (j ≫ p) rfl).hom.app M)))

/-- Over an arbitrary base `B` on which the exponent of `Λ` is invertible: the unit
`Λ_B(1) ⟶ Rπ_* Lπ^* Λ_B(1)` of `π : 𝔾_{m,B} ⟶ B` is an isomorphism on `H⁰`. -/
theorem isIso_homology_zero_unit_tateObject_multiplicativeGroup_of_hasInvertibleExponent
    (B : Scheme.{u}) [HasInvertibleExponent Λ B] :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        ((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι ≫
          𝔸(ULift.{u} (Fin 1); B) ↘ B)).unit.app (tateObject Λ B 1))) := by
  let X := 𝔸(ULift.{u} (Fin 1); B)
  let p := X ↘ B
  let jU := (X.basicOpen (AffineSpace.coord B (ULift.up 0))).ι
  have : HasInvertibleExponent Λ X := .of_hom p
  have hp := isIso_unit_tateObject_affineLine_of_strictlyHenselian Λ B
  refine isIso_homology_zero_unit_comp_of_isIso Λ p jU _ hp ?_
  have h0 := (affineLine_kummer_clauses_of_hasInvertibleExponent Λ B).1
  let tX := leftDerivedUpperStarTateObjectIso (Λ := Λ) p 1
  have e : (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) jU).unit.app
      ((L((p)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ B 1)) =
      tX.hom ≫ (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) jU).unit.app
        (tateObject Λ X 1) ≫
        (L((jU)^*[ModuleCat.{u + 1} Λ]) ⋙ R((jU)_*[ModuleCat.{u + 1} Λ])).map tX.inv := by
    have hnat := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) jU).unit.naturality
      tX.hom
    simp only [Functor.id_map] at hnat
    rw [reassoc_of% hnat]
    simp only [Functor.comp_map, ← Functor.map_comp, Iso.hom_inv_id]
    erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.comp_id]
  rw [e, Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp]
  infer_instance

/-- Over an arbitrary base `B` on which the exponent of `Λ` is invertible:
`R^mπ_* Λ(1) = 0` for `m ≠ 0, 1`, `π : 𝔾_{m,B} ⟶ B`. -/
theorem isZero_homology_rightDerivedLowerStar_tateObject_multiplicativeGroup_of_hasInvertibleExponent
    (B : Scheme.{u}) [HasInvertibleExponent Λ B] (n : ℤ) (h₀ : n ≠ 0) (h₁ : n ≠ 1) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R(((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι ≫
          𝔸(ULift.{u} (Fin 1); B) ↘ B)_*[ModuleCat.{u + 1} Λ])).obj
        (tateObject Λ (𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))) 1))) := by
  let X := 𝔸(ULift.{u} (Fin 1); B)
  let p := X ↘ B
  let jU := (X.basicOpen (AffineSpace.coord B (ULift.up 0))).ι
  have : HasInvertibleExponent Λ X := .of_hom p
  exact ((affineLine_kummer_clauses_of_hasInvertibleExponent Λ B).2.2 n h₀ h₁).of_iso
    ((_root_.DerivedCategory.homologyFunctor _ n).mapIso
      ((R((jU ≫ p)_*[ModuleCat.{u + 1} Λ])).mapIso
          (leftDerivedUpperStarTateObjectIso (Λ := Λ) jU 1).symm ≪≫
        ((rightDerivedLowerStarComp (ModuleCat.{u + 1} Λ) jU p).app _).symm))

/-- Over an arbitrary base `B` on which the exponent of `Λ` is invertible: the unit
`Λ_B ⟶ Rπ_* Lπ^* Λ_B` of `π : 𝔾_{m,B} ⟶ B` is an isomorphism on `H⁰`. This is checked on the
étale cover of `B` adjoining a primitive root of unity, on which `Λ(1) ≅ Λ`
(`AlgebraicGeometry.Etale.isIso_homology_zero_unit_tateObject_multiplicativeGroup_of_hasInvertibleExponent`). -/
theorem isIso_homology_zero_unit_constantComplex_multiplicativeGroup_of_hasInvertibleExponent
    (B : Scheme.{u}) [HasInvertibleExponent Λ B] :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        ((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι ≫
          𝔸(ULift.{u} (Fin 1); B) ↘ B)).unit.app (constantComplex Λ B))) := by
  let g := tateCoverOf Λ B
  have : HasInvertibleExponent Λ (pullback (toInvertibleExponentBase (Λ := Λ) B) (tateCover Λ)) :=
    .of_hom g
  refine isIso_homology_map_of_jointlySurjective Λ (ι := PUnit.{u + 1}) (fun _ ↦ g)
    (fun x ↦ ?_) _ 0 fun _ ↦ ?_
  · obtain ⟨y, hy⟩ := surjective_tateCoverOf Λ B x
    exact ⟨⟨⟩, y, hy⟩
  let V := pullback (toInvertibleExponentBase (Λ := Λ) B) (tateCover Λ)
  let jV := (𝔸(ULift.{u} (Fin 1); V).basicOpen (AffineSpace.coord V (ULift.up 0))).ι
  have hjV := AffineSpace.range_basicOpen_ι_coord V
  have hjU := AffineSpace.range_basicOpen_ι_coord B
  let sq := AffineSpace.isPullback_complementMap_over g _ jV hjU hjV
  have hBC : IsIso ((derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
      ((L(((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι ≫
          𝔸(ULift.{u} (Fin 1); B) ↘ B)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ B))) := by
    have := Etale.isIso_derivedBaseChangeMapPlus_of_etale (Λ := Λ) sq
    refine (NatTrans.isIso_app_iff_of_iso _ (leftDerivedUpperStarConstantComplexIso Λ _ ≪≫
      constantComplexIsoSingleFunctor Λ _)).2 ?_
    exact (isIso_derivedBaseChangeMap_app_ι_obj_iff (ModuleCat.{u + 1} Λ) sq.toCommSq
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (𝟙_ _))).2
      inferInstance
  refine isIso_homology_map_leftDerivedUpperStar_unit_app Λ sq.toCommSq _
    (leftDerivedUpperStarConstantComplexIso Λ g) 0 hBC ?_
  have hT := isIso_homology_zero_unit_tateObject_multiplicativeGroup_of_hasInvertibleExponent Λ V
  let eV : tateObject Λ V 1 ≅ constantComplex Λ V :=
    (leftDerivedUpperStarTateObjectIso (Λ := Λ) g 1).symm ≪≫
      (L((g)^*[ModuleCat.{u + 1} Λ])).mapIso (tateTwistObjectIsoSingleFunctor Λ B 1) ≪≫
      (singleFunctorCompLeftDerivedUpperStarIso _ g).app _ ≪≫
      (_root_.DerivedCategory.singleFunctor _ 0).mapIso
        (upperStarTateCoverOfTateTwistSheafIso Λ B 1) ≪≫
      (constantComplexIsoSingleFunctor Λ V).symm
  exact (NatTrans.isIso_app_iff_of_iso (Functor.whiskerRight
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (jV ≫ 𝔸(ULift.{u} (Fin 1); V) ↘ V)).unit
      (_root_.DerivedCategory.homologyFunctor _ 0)) eV).1 hT

/-- Over an arbitrary base `B` on which the exponent of `Λ` is invertible and for every
identification `β : Lπ^* Λ_B ≅ Λ_G`, the adjoint `Λ_B ⟶ Rπ_*(Λ(1)[1])` of the Kummer class
`κ(t)` of the coordinate of `G = 𝔾_{m,B}` is an isomorphism on `H⁰`. -/
theorem isIso_homology_zero_homEquiv_kummerClass_of_hasInvertibleExponent
    (B : Scheme.{u}) [HasInvertibleExponent Λ B]
    (β : (L(((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι ≫
          𝔸(ULift.{u} (Fin 1); B) ↘ B)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ B) ≅
        constantComplex Λ (𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0)))) :
    IsIso ((_root_.DerivedCategory.homologyFunctor _ 0).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
        ((𝔸(ULift.{u} (Fin 1); B).basicOpen (AffineSpace.coord B (ULift.up 0))).ι ≫
          𝔸(ULift.{u} (Fin 1); B) ↘ B)).homEquiv _ _
        (β.hom ≫ kummerClass Λ
          (𝔸(ULift.{u} (Fin 1); B).basicOpenUnit (AffineSpace.coord B (ULift.up 0)))))) := by
  let X := 𝔸(ULift.{u} (Fin 1); B)
  let t : Γ(X, ⊤) := AffineSpace.coord B (ULift.up 0)
  let p := X ↘ B
  let U := X.basicOpen t
  let jU := U.ι
  let H := _root_.DerivedCategory.homologyFunctor (Sheaf B.smallEtaleTopology
    (ModuleCat.{u + 1} Λ)) 0
  let Rp := R((p)_*[ModuleCat.{u + 1} Λ])
  let θp := leftDerivedUpperStarConstantComplexIso Λ p
  let θj := leftDerivedUpperStarConstantComplexIso Λ jU
  let tU := leftDerivedUpperStarTateObjectIso (Λ := Λ) jU 1
  let κU := kummerClass Λ (X.basicOpenUnit t)
  let α := θj.hom ≫ κU ≫ tU.inv⟦(1 : ℤ)⟧'
  let cs := ((R((jU)_*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.app
    ((L((jU)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ X 1))
  let Ψ₁ := (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).homEquiv _ _
    (θp.hom ≫ (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) jU).homEquiv _ _ α)
  have hκ : kummerClassAffineLineDirectImage Λ B =
      Ψ₁ ≫ Rp.map cs ≫ (Rp.commShiftIso (1 : ℤ)).hom.app _ := by
    simp only [kummerClassAffineLineDirectImage, kummerClassAdjoint, ShiftedHom.map, Ψ₁,
      Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc, α, cs, θp, θj, tU, κU, Rp,
      p, X, t, U, jU]
    rfl
  have hb₁ := (affineLine_kummer_clauses_of_hasInvertibleExponent Λ B).2.1
  have hΨ₁ : IsIso (H.map Ψ₁) := by
    simp only [Functor.shiftMap, hκ, Functor.map_comp, Category.assoc] at hb₁
    rw [isIso_comp_right_iff] at hb₁
    exact hb₁
  let Bι : (L((jU ≫ p)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ B) ≅
      constantComplex Λ U :=
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) jU p (jU ≫ p) rfl).app _ ≪≫
      (L((jU)^*[ModuleCat.{u + 1} Λ])).mapIso θp ≪≫ θj
  let c := (rightDerivedLowerStarCompHom (ModuleCat.{u + 1} Λ) jU p (jU ≫ p) rfl).app
    ((tateObject Λ U 1)⟦(1 : ℤ)⟧)
  have hc : IsIso c := by
    simp only [c]
    rw [← rightDerivedLowerStarComp_hom_comp_congr_hom]
    infer_instance
  have hkey : Ψ₁ ≫ Rp.map ((R((jU)_*[ModuleCat.{u + 1} Λ])).map (tU.hom⟦(1 : ℤ)⟧')) ≫ c =
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (jU ≫ p)).homEquiv _ _
        (Bι.hom ≫ κU) := by
    have h1 : θp.hom ≫ (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) jU).homEquiv
        _ _ α ≫ (R((jU)_*[ModuleCat.{u + 1} Λ])).map (tU.hom⟦(1 : ℤ)⟧') =
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) jU).homEquiv _ _
          ((L((jU)^*[ModuleCat.{u + 1} Λ])).map θp.hom ≫ θj.hom ≫ κU) := by
      rw [← Adjunction.homEquiv_naturality_right, ← Adjunction.homEquiv_naturality_left]
      simp only [α, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
      erw [CategoryTheory.Functor.map_id, Category.comp_id]
    have h2 : Ψ₁ ≫ Rp.map ((R((jU)_*[ModuleCat.{u + 1} Λ])).map (tU.hom⟦(1 : ℤ)⟧')) =
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).comp
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) jU)).homEquiv _ _
          ((L((jU)^*[ModuleCat.{u + 1} Λ])).map θp.hom ≫ θj.hom ≫ κU) := by
      simp only [Ψ₁]
      rw [← Adjunction.homEquiv_naturality_right, Category.assoc, h1,
        Adjunction.comp_homEquiv]
      rfl
    rw [← Category.assoc, h2, Adjunction.homEquiv_comp_conjugateEquiv_app]
    congr 1
    simp only [Bι, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Category.assoc]
  have hgen : IsIso (H.map ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
      (jU ≫ p)).homEquiv _ _ (Bι.hom ≫ κU))) := by
    rw [← hkey, Functor.map_comp, Functor.map_comp]
    infer_instance
  have hunit :=
    isIso_homology_zero_unit_constantComplex_multiplicativeGroup_of_hasInvertibleExponent Λ B
  let u₀ := H.map ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (jU ≫ p)).unit.app
    (constantComplex Λ B))
  have hu₀ : IsIso u₀ := hunit
  have e0 : (R((jU ≫ p)_*[ModuleCat.{u + 1} Λ])).map (β.hom ≫ Bι.inv) ≫
      (R((jU ≫ p)_*[ModuleCat.{u + 1} Λ])).map (Bι.hom ≫ κU) =
      (R((jU ≫ p)_*[ModuleCat.{u + 1} Λ])).map (β.hom ≫ κU) := by
    rw [← Functor.map_comp]
    simp
  have e1 : H.map ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (jU ≫ p)).homEquiv
      _ _ (β.hom ≫ κU)) =
      (u₀ ≫ H.map ((R((jU ≫ p)_*[ModuleCat.{u + 1} Λ])).map (β.hom ≫ Bι.inv)) ≫ inv u₀) ≫
        H.map ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (jU ≫ p)).homEquiv
          _ _ (Bι.hom ≫ κU)) := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, ← e0]
    simp only [u₀, Functor.map_comp, Category.assoc, Functor.id_obj, IsIso.inv_hom_id_assoc]
  rw [e1]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance hgen

end Kummer

end Etale

end AlgebraicGeometry
