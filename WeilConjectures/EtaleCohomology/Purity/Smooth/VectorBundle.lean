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

/-! ### Gluing the frame classes -/

omit [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] [HasInvertibleExponent Λ V] in
/-- On a scheme `W` mapping to two charts, the coordinates of the second chart are an invertible
linear combination of those of the first: this is the linearity of the transition maps. -/
lemma exists_mulVec_coord {W : Scheme.{u}} (i j : E.ι) (a : W ⟶ (π ⁻¹ᵁ E.U i).toScheme)
    (b : W ⟶ (π ⁻¹ᵁ E.U j).toScheme) (hab : a ≫ (π ⁻¹ᵁ E.U i).ι = b ≫ (π ⁻¹ᵁ E.U j).ι) :
    ∃ M : Matrix (Fin d) (Fin d) Γ(W, ⊤), IsUnit M.det ∧
      (fun t ↦ b.appTop (E.coord j t)) = M.mulVec fun t ↦ a.appTop (E.coord i t) := by
  obtain ⟨M, hM, hlin⟩ := E.linear i j
  have hr : Set.range (a ≫ (π ⁻¹ᵁ E.U i).ι).base ⊆
      Set.range (π ⁻¹ᵁ (E.U i ⊓ E.U j)).ι.base := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    have h₁ : (a ≫ (π ⁻¹ᵁ E.U i).ι).base y ∈ π ⁻¹ᵁ E.U i := by
      rw [Scheme.Hom.comp_apply]
      exact (a.base y).2
    have h₂ : (a ≫ (π ⁻¹ᵁ E.U i).ι).base y ∈ π ⁻¹ᵁ E.U j := by
      rw [hab, Scheme.Hom.comp_apply]
      exact (b.base y).2
    exact ⟨h₁, h₂⟩
  let c := IsOpenImmersion.lift (π ⁻¹ᵁ (E.U i ⊓ E.U j)).ι _ hr
  have hc : c ≫ (π ⁻¹ᵁ (E.U i ⊓ E.U j)).ι = a ≫ (π ⁻¹ᵁ E.U i).ι :=
    IsOpenImmersion.lift_fac _ _ _
  have hca : c ≫ V.homOfLE (π.preimage_mono inf_le_left) = a := by
    rw [← cancel_mono (π ⁻¹ᵁ E.U i).ι, Category.assoc, Scheme.homOfLE_ι, hc]
  have hcb : c ≫ V.homOfLE (π.preimage_mono inf_le_right) = b := by
    rw [← cancel_mono (π ⁻¹ᵁ E.U j).ι, Category.assoc, Scheme.homOfLE_ι, hc, hab]
  have key : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : Γ(Z, ⊤)),
      (f ≫ g).appTop x = f.appTop (g.appTop x) := fun f g x ↦ by
    rw [Scheme.Hom.comp_appTop]
    rfl
  refine ⟨M.map (c ≫ π ∣_ (E.U i ⊓ E.U j)).appTop.hom, ?_, ?_⟩
  · rw [← RingHom.map_det]
    exact hM.map _
  · funext t
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, coord]
    rw [← key, ← hcb, Category.assoc, key, hlin t, map_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [map_mul, ← key, ← key, ← key, ← hca, Category.assoc]

omit [HasKummerClass.IsNormalized Λ] [HasInvertibleExponent Λ V] in
/-- **Frame classes agree on overlaps.** Two frames of a closed immersion whose functions differ,
on a scheme `W` étale over both, by an invertible matrix, have the same restriction to `W`
(`AlgebraicGeometry.Etale.restrictSupportedClass_kummerBoundaryProduct_mulVec`). -/
theorem _root_.AlgebraicGeometry.Etale.restrictSupportedClass_frameClass_eq_of_mulVec
    {X Z : Scheme.{u}} {c : ℕ} {i : Z ⟶ X} [IsClosedImmersion i] [HasInvertibleExponent Λ X]
    (F₁ F₂ : i.EtaleFrame c) {W : Scheme.{u}} [HasInvertibleExponent Λ W] (a : W ⟶ F₁.U)
    (b : W ⟶ F₂.U) [AlgebraicGeometry.Etale a] [AlgebraicGeometry.Etale b]
    (M : Matrix (Fin c) (Fin c) Γ(W, ⊤)) (hM : IsUnit M.det)
    (hMf : (fun t ↦ b.appTop (F₂.f t)) = M.mulVec fun t ↦ a.appTop (F₁.f t))
    (g₁ : W.zeroLocusSubscheme (Set.range fun t ↦ a.appTop (F₁.f t)) ⟶ _)
    (hg₁ : IsPullback g₁ (W.zeroLocusSubschemeι (Set.range fun t ↦ a.appTop (F₁.f t)))
      (F₁.U.zeroLocusSubschemeι (Set.range F₁.f)) a)
    (g₂ : W.zeroLocusSubscheme (Set.range fun t ↦ a.appTop (F₁.f t)) ⟶ _)
    (hg₂ : IsPullback g₂ (W.zeroLocusSubschemeι (Set.range fun t ↦ a.appTop (F₁.f t)))
      (F₂.U.zeroLocusSubschemeι (Set.range F₂.f)) b) :
    haveI : HasInvertibleExponent Λ F₁.U := .of_hom F₁.e
    haveI : HasInvertibleExponent Λ F₂.U := .of_hom F₂.e
    restrictSupportedClass (ModuleCat.{u + 1} Λ) a _ _ g₁ hg₁
        (leftDerivedUpperStarConstantComplexIso Λ a).inv (leftDerivedUpperStarTateShiftIso Λ a c)
        (frameClass Λ F₁) =
      restrictSupportedClass (ModuleCat.{u + 1} Λ) b _ _ g₂ hg₂
        (leftDerivedUpperStarConstantComplexIso Λ b).inv (leftDerivedUpperStarTateShiftIso Λ b c)
        (frameClass Λ F₂) := by
  have : HasInvertibleExponent Λ F₁.U := .of_hom F₁.e
  have : HasInvertibleExponent Λ F₂.U := .of_hom F₂.e
  set v : Fin c → Γ(W, ⊤) := fun t ↦ a.appTop (F₁.f t)
  set w : Fin c → Γ(W, ⊤) := fun t ↦ b.appTop (F₂.f t)
  obtain ⟨gw, hgw⟩ : ∃ g, IsPullback g _ _ _ :=
    ⟨_, isPullback_zeroLocusSubschemeι b (Set.range F₂.f) (Set.range w)
      (by rw [← Set.range_comp]; rfl)⟩
  obtain ⟨g₀, hg₀⟩ := Scheme.exists_isPullback_zeroLocusSubschemeι_of_span_eq
    (U := W) (s := Set.range w) (s' := Set.range v)
    (by rw [hMf, Ideal.span_range_mulVec_of_isUnit_det _ hM])
  rw [restrictSupportedClass_comp_tateShift Λ (𝟙 _) b _ (Category.id_comp _).symm _ _ _
    gw hgw g₀ hg₀ g₂ hg₂, frameClass, frameClass,
    restrictSupportedClass_kummerBoundaryProduct Λ a F₁.f v (fun _ ↦ rfl) g₁ hg₁,
    restrictSupportedClass_kummerBoundaryProduct Λ b F₂.f w (fun _ ↦ rfl) gw hgw]
  have key : ∀ (w' : Fin c → Γ(W, ⊤)) (_ : w' = M.mulVec v) (g : _ ⟶ _)
      (hg : IsPullback g (W.zeroLocusSubschemeι (Set.range v))
        (W.zeroLocusSubschemeι (Set.range w')) (𝟙 _)),
      kummerBoundaryProduct Λ v =
        restrictSupportedClass (ModuleCat.{u + 1} Λ) (𝟙 _) _ _ g hg
          (leftDerivedUpperStarConstantComplexIso Λ (𝟙 _)).inv
          (leftDerivedUpperStarTateShiftIso Λ (𝟙 _) c) (kummerBoundaryProduct Λ w') := by
    rintro _ rfl g hg
    exact (restrictSupportedClass_kummerBoundaryProduct_mulVec Λ v M hM g hg).symm
  exact key w hMf g₀ hg₀

/-- The restriction of supports along the inclusion of a chart is invertible. -/
lemma isIso_supportedRestriction_frame (i : E.ι) :
    IsIso (supportedRestriction (ModuleCat.{u + 1} Λ) (E.frame i).e E.zero _ (E.frame i).toZ
      (E.frame i).isPullback _ _ (leftDerivedUpperStarTateShiftIso Λ (E.frame i).e d)) :=
  isIso_supportedRestriction_of_isOpenImmersion _ _ _ _ _ _ _ _ _

/-- The frame classes of the charts glue: there is a class with supports in the zero section
restricting to `∂κ(t₁) ∪ ⋯ ∪ ∂κ(t_d)` on every chart. By
`AlgebraicGeometry.VectorBundle.exists_iso_singleFunctor_thomTarget` classes with supports in
the zero section are sections of a sheaf, and the frame classes agree on overlaps, the
transition maps being linear (`AlgebraicGeometry.Etale.restrictSupportedClass_frameClass_eq_of_mulVec`).
-/
theorem exists_thomClass :
    ∃ γ : constantComplex Λ V ⟶ (R(E.zero)_![ModuleCat.{u + 1} Λ]).obj
        ((R(E.zero)^![ModuleCat.{u + 1} Λ]).obj (thomCoefficients Λ (d := d))),
      ∀ i, frameRestriction Λ (E.frame i) γ = frameClass Λ (E.frame i) := by
  obtain ⟨G, ⟨eM⟩⟩ := E.exists_iso_singleFunctor_thomTarget Λ
  have hΨ := E.isIso_supportedRestriction_frame Λ
  let δ : ∀ i, (L(((E.frame i).e)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ V) ⟶
      (L(((E.frame i).e)^*[ModuleCat.{u + 1} Λ])).obj ((R(E.zero)_![ModuleCat.{u + 1} Λ]).obj
        ((R(E.zero)^![ModuleCat.{u + 1} Λ]).obj (thomCoefficients Λ (d := d)))) := fun i ↦
    (leftDerivedUpperStarConstantComplexIso Λ (E.frame i).e).hom ≫ frameClass Λ (E.frame i) ≫
      inv (supportedRestriction (ModuleCat.{u + 1} Λ) (E.frame i).e E.zero _ (E.frame i).toZ
        (E.frame i).isPullback _ _ (leftDerivedUpperStarTateShiftIso Λ (E.frame i).e d))
  have hδ : ∀ i, δ i ≫ supportedRestriction (ModuleCat.{u + 1} Λ) (E.frame i).e E.zero _
      (E.frame i).toZ (E.frame i).isPullback _ _
        (leftDerivedUpperStarTateShiftIso Λ (E.frame i).e d) =
        (leftDerivedUpperStarConstantComplexIso Λ (E.frame i).e).hom ≫
          frameClass Λ (E.frame i) := by
    intro i
    simp [δ]
  obtain ⟨γ, hγ⟩ := exists_hom_of_isOpenImmersion_cover (constantComplexIsoSingleFunctor Λ V) eM
    (fun i ↦ (E.frame i).e) (fun x ↦ E.mem_range_frame_e x) δ (by
    intro i j W a b _ _ h
    have : HasInvertibleExponent Λ W := .of_hom (a ≫ (E.frame i).e)
    have : HasInvertibleExponent Λ (E.frame i).U := .of_hom (E.frame i).e
    have : HasInvertibleExponent Λ (E.frame j).U := .of_hom (E.frame j).e
    obtain ⟨g₁, hg₁⟩ : ∃ g, IsPullback g _ _ _ :=
      ⟨_, isPullback_zeroLocusSubschemeι a (Set.range (E.frame i).f)
        (Set.range fun t ↦ a.appTop ((E.frame i).f t)) (by rw [← Set.range_comp]; rfl)⟩
    have hg' := hg₁.paste_horiz (E.frame i).isPullback
    have hout : IsPullback (g₁ ≫ (E.frame i).toZ)
        (W.zeroLocusSubschemeι (Set.range fun t ↦ a.appTop ((E.frame i).f t))) E.zero
        (b ≫ (E.frame j).e) := h ▸ hg'
    let g₂ := (E.frame j).isPullback.lift (g₁ ≫ (E.frame i).toZ)
      (W.zeroLocusSubschemeι (Set.range fun t ↦ a.appTop ((E.frame i).f t)) ≫ b)
      (by rw [hout.w, Category.assoc])
    have hg₂ : IsPullback g₂
        (W.zeroLocusSubschemeι (Set.range fun t ↦ a.appTop ((E.frame i).f t))) _ b :=
      IsPullback.of_right (by rw [IsPullback.lift_fst]; exact hout)
        ((E.frame j).isPullback.lift_snd _ _ _) (E.frame j).isPullback
    have := isIso_supportedRestriction_of_isOpenImmersion (ModuleCat.{u + 1} Λ)
      (a ≫ (E.frame i).e) E.zero _ _ hg' _ _ (leftDerivedUpperStarTateShiftIso Λ _ d)
    obtain ⟨M, hM, hMf⟩ := E.exists_mulVec_coord i j a b h
    rw [← cancel_epi (leftDerivedUpperStarConstantComplexIso Λ (a ≫ (E.frame i).e)).inv,
      ← cancel_mono (supportedRestriction (ModuleCat.{u + 1} Λ) (a ≫ (E.frame i).e) E.zero _ _
        hg' _ _ (leftDerivedUpperStarTateShiftIso Λ (a ≫ (E.frame i).e) d))]
    simp only [Category.assoc]
    exact (constantComplexIso_inv_comp_leftDerivedUpperStarComp_map_supportedRestriction Λ
      (E.frame i).e a _ rfl E.zero _ _ (E.frame i).toZ (E.frame i).isPullback g₁ hg₁ _ hg' _ _
        (hδ i)).trans
      ((restrictSupportedClass_frameClass_eq_of_mulVec Λ (E.frame i) (E.frame j) a b M hM hMf
        g₁ hg₁ g₂ hg₂).trans
      (constantComplexIso_inv_comp_leftDerivedUpperStarComp_map_supportedRestriction Λ
        (E.frame j).e b _ h E.zero _ _ (E.frame j).toZ (E.frame j).isPullback g₂ hg₂ _ hg' _ _
          (hδ j)).symm))
  refine ⟨γ, fun i ↦ ?_⟩
  have h : (L(((E.frame i).e)^*[ModuleCat.{u + 1} Λ])).map γ = δ i := hγ i
  simp only [frameRestriction, restrictSupportedClass, h, δ, Category.assoc, IsIso.inv_hom_id,
    Category.comp_id, Iso.inv_hom_id_assoc]

/-- Blueprint `def-pur-vector-bundle-thom-class`: the *Thom class*
`th(V) ∈ H^{2d}_{z(S)}(V, Λ(d))` of a vector bundle, the class with supports in the zero section
restricting to `∂κ(t₁) ∪ ⋯ ∪ ∂κ(t_d)` on every chart
(`AlgebraicGeometry.VectorBundle.frameRestriction_thomClass`). -/
noncomputable def thomClass : constantComplex Λ V ⟶ (R(E.zero)_![ModuleCat.{u + 1} Λ]).obj
    ((R(E.zero)^![ModuleCat.{u + 1} Λ]).obj (thomCoefficients Λ (d := d))) :=
  (E.exists_thomClass Λ).choose

/-- The Thom class restricts to the frame class on every chart. -/
lemma frameRestriction_thomClass (i : E.ι) :
    frameRestriction Λ (E.frame i) (E.thomClass Λ) = frameClass Λ (E.frame i) :=
  (E.exists_thomClass Λ).choose_spec i

/-- The adjoint `Λ_S ⟶ Rz^! (Λ_V(d)[2d])` of the Thom class. -/
noncomputable def thomClassMap : constantComplex Λ S ⟶
    (R(E.zero)^![ModuleCat.{u + 1} Λ]).obj (thomCoefficients Λ (d := d)) :=
  supportedClassMap Λ E.zero (E.thomClass Λ)

/-- **The Thom isomorphism.** The adjoint `Λ_S ⟶ Rz^! (Λ_V(d)[2d])` of the Thom class is an
isomorphism: over every chart it is the adjoint of the class of the zero section of `𝔸^d_U`
(`AlgebraicGeometry.VectorBundle.isIso_supportedClassMap_frameClass`). -/
theorem isIso_thomClassMap : IsIso (E.thomClassMap Λ) := by
  refine isIso_of_isIso_leftDerivedUpperStar_map_of_jointlySurjective Λ
    (fun i ↦ (E.frame i).toZ) (fun s ↦ ?_) _ fun i ↦ ?_
  · obtain ⟨i, y, hy⟩ := E.mem_range_frame_toZ s
    exact ⟨i, y, hy⟩
  · refine (isIso_supportedClassMap_restrictSupportedClass_iff Λ (E.frame i).e E.zero _
      (E.frame i).toZ (E.frame i).isPullback _ _ _ (E.thomClass Λ)
      (E.isIso_supportedRestriction_frame Λ i)).1 ?_
    have h := E.frameRestriction_thomClass Λ i
    rw [frameRestriction] at h
    rw [h]
    exact E.isIso_supportedClassMap_frameClass Λ i

end Thom

end VectorBundle

end AlgebraicGeometry
