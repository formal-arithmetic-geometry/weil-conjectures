/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorBundle
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersionIso
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Local

/-!
# The Thom class of a vector bundle

Let `π : V ⟶ S` be a vector bundle of rank `d` (`AlgebraicGeometry.VectorBundle`) with zero
section `z`, over a scheme on which the exponent of the finite coefficient ring `Λ` is
invertible. Over a trivialising open `U ⊆ S`, with coordinates `t₁, …, t_d` on `π⁻¹ U`, the zero
section is the closed subscheme `V(t₁, …, t_d)`, and the cup product with supports
`∂κ(t₁) ∪ ⋯ ∪ ∂κ(t_d)` of the Kummer boundaries of the coordinates is a class in
`H^{2d}_{z(U)}(π⁻¹ U, Λ(d))`. A second chart has coordinates `M t` for an invertible matrix `M`,
and the class does not change
(`AlgebraicGeometry.Etale.restrictSupportedClass_kummerBoundaryProduct_mulVec`).
Since `Rz^! Λ(d)[2d]` is concentrated in degree zero, classes with supports in the zero section
are sections of a sheaf, and the local classes glue to the *Thom class*
`th(V) ∈ H^{2d}_{z(S)}(V, Λ(d))`, whose adjoint `Λ_S ⟶ Rz^! (Λ_V(d)[2d])` is an isomorphism.

## Main definitions

- `AlgebraicGeometry.VectorBundle.frame`: the frame of the zero section given by a chart.
- `AlgebraicGeometry.VectorBundle.thomClass`: the Thom class.
- `AlgebraicGeometry.VectorBundle.thomClassMap`: its adjoint `Λ_S ⟶ Rz^! (Λ_V(d)[2d])`.

## Main statements

- `AlgebraicGeometry.VectorBundle.existsUnique_thomClass`: the local classes glue uniquely.
- `AlgebraicGeometry.VectorBundle.isIso_thomClassMap`: the Thom isomorphism
  `Λ_S ≅ Rz^! (Λ_V(d)[2d])`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

namespace VectorBundle

variable {V S : Scheme.{u}} {d : ℕ} {π : V ⟶ S} (E : VectorBundle d π)

/-! ### The frames of the zero section given by the charts -/

/-- The coordinates of affine space over a trivialising open. -/
noncomputable abbrev affineCoord (i : E.ι) : Fin d → Γ(𝔸(ULift.{u} (Fin d); E.U i), ⊤) :=
  fun a ↦ AffineSpace.coord _ (ULift.up a)

lemma range_coord_eq (i : E.ι) :
    Set.range (AffineSpace.coord (E.U i).toScheme : ULift.{u} (Fin d) → _) =
      Set.range (E.affineCoord i) := by
  ext x
  constructor
  · rintro ⟨⟨a⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨a⟩, rfl⟩

lemma image_coord (i : E.ι) :
    (E.chart i).hom.appTop '' Set.range (E.affineCoord i) = Set.range (E.coord i) := by
  rw [← Set.range_comp]
  rfl

/-- The chart identifies the zero locus of its coordinates with that of affine space. -/
lemma isPullback_chart (i : E.ι) :
    IsPullback ((E.chart i).hom.zeroLocusSubschemeMap _ _ (E.image_coord i))
      ((π ⁻¹ᵁ E.U i).toScheme.zeroLocusSubschemeι (Set.range (E.coord i)))
      (𝔸(ULift.{u} (Fin d); E.U i).zeroLocusSubschemeι (Set.range (E.affineCoord i)))
      (E.chart i).hom :=
  isPullback_zeroLocusSubschemeι _ _ _ (E.image_coord i)

instance (i : E.ι) : IsIso ((E.chart i).hom.zeroLocusSubschemeMap _ _ (E.image_coord i)) :=
  (E.isPullback_chart i).isIso_fst_of_isIso

/-- The zero locus of the coordinates of the `i`-th chart is the trivialising open `U i`. -/
noncomputable def chartZeroLocusIso (i : E.ι) :
    (π ⁻¹ᵁ E.U i).toScheme.zeroLocusSubscheme (Set.range (E.coord i)) ≅ (E.U i).toScheme :=
  asIso ((E.chart i).hom.zeroLocusSubschemeMap _ _ (E.image_coord i)) ≪≫
    (AffineSpace.zeroSectionIsoZeroLocusSubscheme _ _ (E.range_coord_eq i)).symm

@[reassoc (attr := simp)]
lemma chartZeroLocusIso_inv_zeroLocusSubschemeι (i : E.ι) :
    (E.chartZeroLocusIso i).inv ≫
        (π ⁻¹ᵁ E.U i).toScheme.zeroLocusSubschemeι (Set.range (E.coord i)) =
      E.zeroRestrict i := by
  rw [zeroRestrict_eq, ← cancel_mono (E.chart i).hom, Category.assoc, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, ← (E.isPullback_chart i).w]
  simp only [chartZeroLocusIso, Iso.trans_inv, Iso.symm_inv, asIso_inv, Category.assoc,
    IsIso.inv_hom_id_assoc, AffineSpace.zeroSectionIsoZeroLocusSubscheme_hom_zeroLocusSubschemeι]

/-- Over a trivialising open, the zero section is the base change of `z` along the inclusion
of `π⁻¹ U`. -/
lemma isPullback_zeroRestrict (i : E.ι) :
    IsPullback (E.U i).ι (E.zeroRestrict i) E.zero (π ⁻¹ᵁ E.U i).ι := by
  have e := E.preimage_zero_preimage (E.U i)
  refine IsPullback.of_iso (isPullback_morphismRestrict E.zero (π ⁻¹ᵁ E.U i)).flip
    (S.isoOfEq e) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · simp
  · rw [← cancel_mono (π ⁻¹ᵁ E.U i).ι]
    simp [zeroRestrict, Scheme.Hom.resLE]
  · simp
  · simp

/-- The frame of the zero section given by the `i`-th chart: the open `π⁻¹(U i)` with the
coordinates of the chart, whose zero locus is the zero section over `U i`. -/
@[simps]
noncomputable def frame (i : E.ι) : E.zero.EtaleFrame d where
  U := (π ⁻¹ᵁ E.U i).toScheme
  e := (π ⁻¹ᵁ E.U i).ι
  etale := inferInstance
  f := E.coord i
  toZ := (E.chartZeroLocusIso i).hom ≫ (E.U i).ι
  isPullback := by
    refine IsPullback.of_iso (E.isPullback_zeroRestrict i) (E.chartZeroLocusIso i).symm
      (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp

instance (i : E.ι) : IsOpenImmersion (E.frame i).e :=
  inferInstanceAs (IsOpenImmersion (π ⁻¹ᵁ E.U i).ι)

lemma mem_range_frame_toZ (s : S) : ∃ i, s ∈ Set.range (E.frame i).toZ := by
  have hs : s ∈ iSup E.U := by rw [E.iSup_U]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hs
  obtain ⟨t, rfl⟩ : s ∈ Set.range (E.U i).ι.base := by rw [Scheme.Opens.range_ι]; exact hi
  refine ⟨i, (E.chartZeroLocusIso i).inv t, ?_⟩
  change ((E.chartZeroLocusIso i).inv ≫ (E.chartZeroLocusIso i).hom ≫ (E.U i).ι).base t = _
  rw [Iso.inv_hom_id_assoc]

lemma mem_range_frame_e (x : V) : ∃ i, x ∈ Set.range (E.frame i).e := by
  have hx : x ∈ ⨆ i, π ⁻¹ᵁ E.U i := by rw [E.iSup_preimage_U]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨i, by
    change x ∈ Set.range (π ⁻¹ᵁ E.U i).ι
    rw [Scheme.Opens.range_ι]
    exact hi⟩

/-! ### Sheaves placed in degree zero under the extension by zero of a closed immersion -/

section ClosedImmersion

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

omit [Finite Λ] in
/-- For a closed immersion `i`, `Ri_!` carries complexes concentrated in degree zero to complexes
concentrated in degree zero: it is the exact direct image `i_*`. -/
lemma _root_.AlgebraicGeometry.Etale.isZero_homology_rightDerivedLowerShriek_of_isClosedImmersion
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (K : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    [K.IsGE 0] [K.IsLE 0] (n : ℤ) (hn : n ≠ 0) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R(i)_![ModuleCat.{u + 1} Λ]).obj K)) := by
  have := Etale.preservesFiniteColimits_lowerStar_of_isIntegralHom Λ i
  obtain ⟨e⟩ := nonempty_iso_rightDerivedLowerShriek_rightDerivedLowerStar
    (ModuleCat.{u + 1} Λ) i
  have : (((i)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj K).IsGE 0 :=
    ((i)_*[ModuleCat.{u + 1} Λ]).isGE_mapDerivedCategory_obj K 0
  have : (((i)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj K).IsLE 0 :=
    ((i)_*[ModuleCat.{u + 1} Λ]).isLE_mapDerivedCategory_obj K 0
  refine IsZero.of_iso ?_ ((_root_.DerivedCategory.homologyFunctor _ n).mapIso (e.app K ≪≫
    ((i)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorIsoMapDerivedCategory.app K))
  rcases lt_or_gt_of_ne hn with h | h
  · exact (((i)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj K).isZero_of_isGE 0 n h
  · exact (((i)_*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj K).isZero_of_isLE 0 n h

end ClosedImmersion

/-! ### The Thom class -/

section Thom

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] [HasInvertibleExponent Λ V]

attribute [local instance] HasInvertibleExponent.opens

/-- The coefficients `Λ_V(d)[2d]` of the Thom class. -/
noncomputable abbrev thomCoefficients : _root_.DerivedCategory
    (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (tateObject Λ V d)⟦2 * (d : ℤ)⟧

/-- The class of the frame of a chart, `∂κ(t₁) ∪ ⋯ ∪ ∂κ(t_d)`, generates: its adjoint
`Λ_{U} ⟶ R(z_U)^! Λ(d)[2d]` is an isomorphism. The chart identifies it with the class of the
zero section of `𝔸^d_U` (`sk-prop-an`,
`AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundaryProduct_coord`). -/
theorem isIso_supportedClassMap_frameClass (i : E.ι) :
    IsIso (supportedClassMap Λ
      ((π ⁻¹ᵁ E.U i).toScheme.zeroLocusSubschemeι (Set.range (E.coord i)))
      (frameClass Λ (E.frame i))) := by
  have : HasInvertibleExponent Λ (π ⁻¹ᵁ E.U i).toScheme := .of_hom (π ⁻¹ᵁ E.U i).ι
  have : HasInvertibleExponent Λ (E.U i).toScheme := .of_hom (E.zeroRestrict i)
  have hmodel := isIso_supportedClassMap_kummerBoundaryProduct_coord Λ d (E.U i)
  have h₁ := restrictSupportedClass_kummerBoundaryProduct Λ (E.chart i).hom (E.affineCoord i)
    (E.coord i) (fun _ ↦ rfl) _ (E.isPullback_chart i)
  have hψ := isIso_supportedRestriction_of_etale Λ (E.chart i).hom _ _ _ (E.isPullback_chart i)
    ((tateObject Λ _ d)⟦2 * (d : ℤ)⟧) ((tateObject Λ _ d)⟦2 * (d : ℤ)⟧)
    (leftDerivedUpperStarTateShiftIso Λ (E.chart i).hom d)
  change IsIso (supportedClassMap Λ _ (kummerBoundaryProduct Λ (E.coord i)))
  rw [← h₁]
  exact (isIso_supportedClassMap_restrictSupportedClass_iff Λ _ _ _ _ (E.isPullback_chart i) _ _
    _ _ hψ).2 inferInstance

/-- `Rz_! Rz^! Λ_V(d)[2d]` is concentrated in degree zero: over the chart `π⁻¹ U`, it is the
extension by zero of `Λ_U` along the zero section. -/
theorem isZero_homology_thomTarget (n : ℤ) (hn : n ≠ 0) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ n).obj
      ((R(E.zero)_![ModuleCat.{u + 1} Λ]).obj
        ((R(E.zero)^![ModuleCat.{u + 1} Λ]).obj (thomCoefficients Λ (d := d))))) := by
  refine isZero_homology_of_jointlySurjective Λ (fun i ↦ (E.frame i).e) (fun x ↦ ?_) _ n
    fun i ↦ ?_
  · obtain ⟨i, y, hy⟩ := E.mem_range_frame_e x
    exact ⟨i, y, hy⟩
  have hψ := isIso_supportedRestriction_of_isOpenImmersion (ModuleCat.{u + 1} Λ) (E.frame i).e
    E.zero _ (E.frame i).toZ (E.frame i).isPullback _ _
    (leftDerivedUpperStarTateShiftIso Λ (E.frame i).e d)
  have hφ : IsIso (supportedClassMap Λ ((E.frame i).U.zeroLocusSubschemeι (Set.range (E.frame i).f))
      (frameClass Λ (E.frame i))) := E.isIso_supportedClassMap_frameClass Λ i
  have : (constantComplex Λ ((E.frame i).U.zeroLocusSubscheme
      (Set.range (E.frame i).f))).IsGE 0 :=
    (_root_.DerivedCategory.isGE_iff _ 0).2 fun n hn ↦ isZero_homology_constantComplex Λ _ n hn.ne
  have : (constantComplex Λ ((E.frame i).U.zeroLocusSubscheme
      (Set.range (E.frame i).f))).IsLE 0 :=
    (_root_.DerivedCategory.isLE_iff _ 0).2 fun n hn ↦ isZero_homology_constantComplex Λ _ n hn.ne'
  exact (isZero_homology_rightDerivedLowerShriek_of_isClosedImmersion Λ _ _ n hn).of_iso
    ((_root_.DerivedCategory.homologyFunctor _ n).mapIso (asIso (supportedRestriction _ _ _ _ _
      (E.frame i).isPullback _ _ (leftDerivedUpperStarTateShiftIso Λ (E.frame i).e d)) ≪≫
        (R(_)_![ModuleCat.{u + 1} Λ]).mapIso (asIso (supportedClassMap Λ _
          (frameClass Λ (E.frame i)))).symm))

/-- Classes with supports in the zero section are sections of a sheaf:
`Rz_! Rz^! Λ_V(d)[2d]` is a sheaf placed in degree zero. -/
theorem exists_iso_singleFunctor_thomTarget :
    ∃ G : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      Nonempty ((R(E.zero)_![ModuleCat.{u + 1} Λ]).obj
          ((R(E.zero)^![ModuleCat.{u + 1} Λ]).obj (thomCoefficients Λ (d := d))) ≅
        (_root_.DerivedCategory.singleFunctor _ 0).obj G) := by
  set K := (R(E.zero)_![ModuleCat.{u + 1} Λ]).obj
    ((R(E.zero)^![ModuleCat.{u + 1} Λ]).obj (thomCoefficients Λ (d := d)))
  have hK := E.isZero_homology_thomTarget Λ
  have : K.IsGE 0 := (_root_.DerivedCategory.isGE_iff K 0).2 fun n hn ↦ hK n hn.ne
  have : K.IsLE 0 := (_root_.DerivedCategory.isLE_iff K 0).2 fun n hn ↦ hK n hn.ne'
  exact _root_.DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K 0

end Thom

end VectorBundle

end AlgebraicGeometry
