/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.VectorBundlePullback
public import WeilConjectures.EtaleCohomology.Purity.Smooth.VectorBundle

/-!
# The localized top Chern class of a section of a vector bundle

Let `π : V ⟶ T` be a vector bundle of rank `r` (`AlgebraicGeometry.VectorBundle`) and
`s : T ⟶ V` a section, with zero scheme `Z(s) = s⁻¹(0) ⊆ T`. The *localized top Chern class*

`c_r(V, s) ∈ H^{2r}_{Z(s)}(T, Λ(r))`

is the restriction of supports along `s` of the Thom class `th(V) ∈ H^{2r}_{0}(V, Λ(r))`
(`AlgebraicGeometry.VectorBundle.thomClass`). Over a chart `π⁻¹ U ≅ 𝔸^r_U`, in which `s` has
components `s₁, …, s_r ∈ Γ(U, 𝒪)`, it is the cup product with supports
`∂κ(s₁) ∪ ⋯ ∪ ∂κ(s_r)` of the Kummer boundaries of the components
(`AlgebraicGeometry.VectorBundle.restrictSupportedClass_localizedTopChern`); for `r = 1` this is
the localized Kummer class of the divisor of `s`. This is the construction of Step 3 of the
blueprint's proof (`thm-pur-localized-top-chern`), where the local classes are glued by frame
independence; here the gluing has been done once and for all for the Thom class.

## Main definitions

- `AlgebraicGeometry.VectorBundle.sectionRes`: a section over a trivialising open.
- `AlgebraicGeometry.VectorBundle.sectionCoord`: the components of a section in a chart.
- `AlgebraicGeometry.VectorBundle.localizedTopChern`: the localized top Chern class.

## Main statements

- `AlgebraicGeometry.VectorBundle.restrictSupportedClass_localizedTopChern`: (L1), the class in
  a chart.
- `AlgebraicGeometry.VectorBundle.restrictSupportedClass_localizedTopChern_comp`,
  `AlgebraicGeometry.VectorBundle.restrictSupportedClass_localizedTopChern_ofIsPullback`: (L2),
  base change.
- (L3), direct sums: `AlgebraicGeometry.VectorBundle.localizedTopChern_sum` in
  `WeilConjectures.EtaleCohomology.Purity.Smooth.VectorBundleSumThom`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme Etale

namespace VectorBundle

variable {V T : Scheme.{u}} {r : ℕ} {π : V ⟶ T} (E : VectorBundle r π) (s : T ⟶ V)
  (hs : s ≫ π = 𝟙 T)

/-- The section `s` over the trivialising open `U i`, `U i ⟶ π⁻¹(U i)`. -/
noncomputable def sectionRes (i : E.ι) : (E.U i).toScheme ⟶ (π ⁻¹ᵁ E.U i).toScheme :=
  s.resLE (π ⁻¹ᵁ E.U i) (E.U i) (Scheme.Hom.le_preimage_preimage_of_comp_eq_id hs _)

@[reassoc (attr := simp)]
lemma sectionRes_ι (i : E.ι) : E.sectionRes s hs i ≫ (π ⁻¹ᵁ E.U i).ι = (E.U i).ι ≫ s :=
  Scheme.Hom.resLE_comp_ι _ _

/-- The components `s₁, …, s_r ∈ Γ(U i, 𝒪)` of the section `s` in the `i`-th chart. -/
noncomputable def sectionCoord (i : E.ι) : Fin r → Γ((E.U i).toScheme, ⊤) :=
  fun a ↦ (E.sectionRes s hs i).appTop (E.coord i a)

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ] [HasInvertibleExponent Λ V]
  {k : Type u} [Field k] (aT : T ⟶ Spec (.of k)) [IsSeparated aT] [LocallyOfFiniteType aT]

attribute [local instance] HasInvertibleExponent.opens

/-- Blueprint `thm-pur-localized-top-chern`: the *localized top Chern class*
`c_r(V, s) ∈ H^{2r}_{Z(s)}(T, Λ(r))` of a section `s` of a vector bundle `π : V ⟶ T` of rank
`r`, supported on the zero scheme `Z(s) = s⁻¹(0)`: the restriction of supports along `s` of the
Thom class (`AlgebraicGeometry.VectorBundle.thomClass`). Its properties are
`AlgebraicGeometry.VectorBundle.restrictSupportedClass_localizedTopChern` (in a chart, the cup
product of the Kummer boundaries of the components; for `r = 1` the localized Kummer class of
the divisor, (L1)) and
`AlgebraicGeometry.VectorBundle.restrictSupportedClass_localizedTopChern_comp`
(base change, (L2)). -/
noncomputable def localizedTopChern :
    haveI : HasInvertibleExponent Λ T := .of_hom E.zero
    constantComplex Λ T ⟶ (R(pullback.snd E.zero s)_![ModuleCat.{u + 1} Λ]).obj
      ((R(pullback.snd E.zero s)^![ModuleCat.{u + 1} Λ]).obj
        ((tateObject Λ T r)⟦2 * (r : ℤ)⟧)) :=
  haveI : HasInvertibleExponent Λ T := .of_hom E.zero
  restrictSupportedClass (ModuleCat.{u + 1} Λ) s E.zero (pullback.snd E.zero s)
    (pullback.fst E.zero s) (IsPullback.of_hasPullback E.zero s)
    (leftDerivedUpperStarConstantComplexIso Λ s).inv (leftDerivedUpperStarTateShiftIso Λ s r)
    (E.thomClass Λ aT)

/-- Blueprint `thm-pur-localized-top-chern`: Localized top Chern class

*(L1), the class in a chart.* Over the trivialising open `U i`, in which the section `s` has
components `s₁, …, s_r`, the localized top Chern class restricts to the cup product with
supports `∂κ(s₁) ∪ ⋯ ∪ ∂κ(s_r)` of the Kummer boundaries of the components. For `r = 1` this is
the localized Kummer class of the Cartier divisor of `s`. The class does not depend on the chart
by frame independence
(`AlgebraicGeometry.Etale.restrictSupportedClass_kummerBoundaryProduct_mulVec`),
which is how the blueprint glues it. -/
theorem restrictSupportedClass_localizedTopChern (i : E.ι)
    (g' : (E.U i).toScheme.zeroLocusSubscheme (Set.range (E.sectionCoord s hs i)) ⟶
      pullback E.zero s)
    (hg' : IsPullback g' ((E.U i).toScheme.zeroLocusSubschemeι
      (Set.range (E.sectionCoord s hs i))) (pullback.snd E.zero s) (E.U i).ι) :
    haveI : HasInvertibleExponent Λ T := .of_hom E.zero
    restrictSupportedClass (ModuleCat.{u + 1} Λ) (E.U i).ι (pullback.snd E.zero s) _ g' hg'
        (leftDerivedUpperStarConstantComplexIso Λ _).inv
        (leftDerivedUpperStarTateShiftIso Λ _ r) (E.localizedTopChern s Λ aT) =
      kummerBoundaryProduct Λ (E.sectionCoord s hs i) := by
  have : HasInvertibleExponent Λ T := .of_hom E.zero
  have : HasInvertibleExponent Λ (π ⁻¹ᵁ E.U i).toScheme := .of_hom (π ⁻¹ᵁ E.U i).ι
  have hout := hg'.paste_horiz (IsPullback.of_hasPullback E.zero s)
  have h₁ := restrictSupportedClass_comp_tateShift Λ (E.U i).ι s ((E.U i).ι ≫ s) rfl
    E.zero (pullback.snd E.zero s) _ (pullback.fst E.zero s) (IsPullback.of_hasPullback E.zero s)
    g' hg' _ hout (E.thomClass Λ aT)
  have hgs := isPullback_zeroLocusSubschemeι (E.sectionRes s hs i)
    (Set.range (E.coord i)) (Set.range (E.sectionCoord s hs i))
    (by rw [← Set.range_comp]; rfl)
  have h₂ := restrictSupportedClass_comp_tateShift Λ (E.sectionRes s hs i) (π ⁻¹ᵁ E.U i).ι
    ((E.U i).ι ≫ s) (E.sectionRes_ι s hs i).symm E.zero _ _ (E.frame i).toZ
    (E.frame i).isPullback _ hgs _ hout (E.thomClass Λ aT)
  have h₃ := E.frameRestriction_thomClass Λ aT i
  rw [frameRestriction] at h₃
  rw [localizedTopChern, ← h₁, h₂]
  erw [h₃]
  exact restrictSupportedClass_kummerBoundaryProduct Λ (E.sectionRes s hs i) (E.coord i)
    (E.sectionCoord s hs i) (fun _ ↦ rfl) _ hgs

/-- Blueprint `thm-pur-localized-top-chern`: Localized top Chern class

*(L2), base change.* For `g : T' ⟶ T`, the restriction of supports along `g` of the localized
top Chern class of `s` is the restriction of the Thom class along the pulled-back section
`g ≫ s`, which is the localized top Chern class of the pulled-back section of the pulled-back
bundle; its support is the base change `g⁻¹ Z(s)` of the zero scheme. -/
theorem restrictSupportedClass_localizedTopChern_comp {T' : Scheme.{u}} (g : T' ⟶ T)
    [HasInvertibleExponent Λ T'] {Z' : Scheme.{u}} (i' : Z' ⟶ T') [IsClosedImmersion i']
    (g₁ : Z' ⟶ pullback E.zero s) (hg₁ : IsPullback g₁ i' (pullback.snd E.zero s) g)
    (g₂ : Z' ⟶ T) (hg₂ : IsPullback g₂ i' E.zero (g ≫ s)) :
    haveI : HasInvertibleExponent Λ T := .of_hom E.zero
    restrictSupportedClass (ModuleCat.{u + 1} Λ) g (pullback.snd E.zero s) i' g₁ hg₁
        (leftDerivedUpperStarConstantComplexIso Λ _).inv
        (leftDerivedUpperStarTateShiftIso Λ _ r) (E.localizedTopChern s Λ aT) =
      restrictSupportedClass (ModuleCat.{u + 1} Λ) (g ≫ s) E.zero i' g₂ hg₂
        (leftDerivedUpperStarConstantComplexIso Λ _).inv
        (leftDerivedUpperStarTateShiftIso Λ _ r) (E.thomClass Λ aT) := by
  have : HasInvertibleExponent Λ T := .of_hom E.zero
  rw [localizedTopChern, ← restrictSupportedClass_comp_tateShift Λ g s (g ≫ s) rfl E.zero
    (pullback.snd E.zero s) i' (pullback.fst E.zero s) (IsPullback.of_hasPullback E.zero s)
    g₁ hg₁ g₂ hg₂ (E.thomClass Λ aT)]
/-! ### Base change of the Thom class -/

section BaseChange

variable {V' S' : Scheme.{u}} {d : ℕ} {π₀ : V ⟶ T} (F : VectorBundle d π₀) {g : S' ⟶ T}
  {g' : V' ⟶ V} {π' : V' ⟶ S'} (sq : IsPullback g' π' π₀ g)

include sq in
/-- The zero section of the base change is the base change of the zero section. -/
lemma isPullback_zero_ofIsPullback : IsPullback g (F.ofIsPullback sq).zero F.zero g' := by
  have h : IsPullback g ((F.ofIsPullback sq).zero ≫ π') (F.zero ≫ π₀) g := by
    rw [ofIsPullback_zero, zeroOfIsPullback_comp, zero_comp]
    exact IsPullback.of_vert_isIso ⟨by simp⟩
  exact IsPullback.of_bot h (F.zeroOfIsPullback_g' sq).symm sq

variable (aS' : S' ⟶ Spec (.of k)) [IsSeparated aS'] [LocallyOfFiniteType aS']

include aT in
/-- Blueprint `def-pur-vector-bundle-thom-class`: the Thom class commutes with base change: the
restriction of supports along `g' : V' ⟶ V` of the Thom class of `V` is the Thom class of the
base change `V' = V ×_T S'`. Both restrict to the frame class of the base changed coordinates on
every chart. -/
theorem restrictSupportedClass_thomClass_ofIsPullback :
    haveI : HasInvertibleExponent Λ V' := .of_hom g'
    restrictSupportedClass (ModuleCat.{u + 1} Λ) g' F.zero (F.ofIsPullback sq).zero g
        (F.isPullback_zero_ofIsPullback sq) (leftDerivedUpperStarConstantComplexIso Λ g').inv
        (leftDerivedUpperStarTateShiftIso Λ g' d) (F.thomClass Λ aT) =
      (F.ofIsPullback sq).thomClass Λ aS' := by
  have : HasInvertibleExponent Λ V' := .of_hom g'
  refine (F.ofIsPullback sq).eq_thomClass_of_frameRestriction Λ aS' fun i ↦ ?_
  have : HasInvertibleExponent Λ (π₀ ⁻¹ᵁ F.U i).toScheme := .of_hom (π₀ ⁻¹ᵁ F.U i).ι
  have hout := ((F.ofIsPullback sq).frame i).isPullback.paste_horiz
    (F.isPullback_zero_ofIsPullback sq)
  have he : ((F.ofIsPullback sq).frame i).e ≫ g' = resPullback sq (F.U i) ≫ (F.frame i).e :=
    (resPullback_ι sq (F.U i)).symm
  have hgs := isPullback_zeroLocusSubschemeι (resPullback sq (F.U i))
    (Set.range (F.frame i).f) (Set.range ((F.ofIsPullback sq).frame i).f) (by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext fun a ↦ (F.ofIsPullback_coord sq i a).symm))
  have h₁ := restrictSupportedClass_comp_tateShift Λ ((F.ofIsPullback sq).frame i).e g' _ rfl
    F.zero (F.ofIsPullback sq).zero _ g (F.isPullback_zero_ofIsPullback sq)
    ((F.ofIsPullback sq).frame i).toZ ((F.ofIsPullback sq).frame i).isPullback _ hout
    (F.thomClass Λ aT)
  have h₂ := restrictSupportedClass_comp_tateShift Λ (resPullback sq (F.U i)) (F.frame i).e _ he
    F.zero _ _ (F.frame i).toZ (F.frame i).isPullback _ hgs _ hout (F.thomClass Λ aT)
  have h₃ := F.frameRestriction_thomClass Λ aT i
  rw [frameRestriction] at h₃
  rw [frameRestriction, ← h₁]
  erw [h₂]
  erw [h₃]
  exact restrictSupportedClass_kummerBoundaryProduct Λ (resPullback sq (F.U i)) (F.coord i)
    ((F.ofIsPullback sq).coord i) (fun a ↦ (F.ofIsPullback_coord sq i a).symm) _ hgs

variable {s₀ : T ⟶ V} (hs₀ : s₀ ≫ π₀ = 𝟙 T)

/-- The base change `S' ⟶ V'` of a section `s₀` of `π₀`. -/
noncomputable def sectionOfIsPullback : S' ⟶ V' :=
  sq.lift (g ≫ s₀) (𝟙 S') (by rw [Category.assoc, hs₀, Category.comp_id, Category.id_comp])

@[reassoc (attr := simp)]
lemma sectionOfIsPullback_g' : sectionOfIsPullback sq hs₀ ≫ g' = g ≫ s₀ :=
  sq.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma sectionOfIsPullback_π' : sectionOfIsPullback sq hs₀ ≫ π' = 𝟙 S' :=
  sq.lift_snd _ _ _

include aT in
/-- Blueprint `thm-pur-localized-top-chern`: Localized top Chern class

*(L2), base change.* For a cartesian square `V' = V ×_T S'` with `g : S' ⟶ T`, the restriction
of supports along `g` of the localized top Chern class of a section `s₀` of `V` is the localized
top Chern class of the base changed section `s₀'` of the base changed bundle `V'`
(`AlgebraicGeometry.VectorBundle.ofIsPullback`); its support `Z(s₀') = g⁻¹ Z(s₀)`. -/
theorem restrictSupportedClass_localizedTopChern_ofIsPullback
    (g₁ : pullback (F.ofIsPullback sq).zero (sectionOfIsPullback sq hs₀) ⟶ pullback F.zero s₀)
    (hg₁ : IsPullback g₁ (pullback.snd (F.ofIsPullback sq).zero (sectionOfIsPullback sq hs₀))
      (pullback.snd F.zero s₀) g) :
    haveI : HasInvertibleExponent Λ T := .of_hom F.zero
    haveI : HasInvertibleExponent Λ V' := .of_hom g'
    haveI : HasInvertibleExponent Λ S' := .of_hom (F.ofIsPullback sq).zero
    restrictSupportedClass (ModuleCat.{u + 1} Λ) g (pullback.snd F.zero s₀) _ g₁ hg₁
        (leftDerivedUpperStarConstantComplexIso Λ _).inv
        (leftDerivedUpperStarTateShiftIso Λ _ d) (F.localizedTopChern s₀ Λ aT) =
      (F.ofIsPullback sq).localizedTopChern (sectionOfIsPullback sq hs₀) Λ aS' := by
  have : HasInvertibleExponent Λ T := .of_hom F.zero
  have : HasInvertibleExponent Λ V' := .of_hom g'
  have : HasInvertibleExponent Λ S' := .of_hom (F.ofIsPullback sq).zero
  have hout := hg₁.paste_horiz (IsPullback.of_hasPullback F.zero s₀)
  have hout' : IsPullback (g₁ ≫ pullback.fst F.zero s₀)
      (pullback.snd (F.ofIsPullback sq).zero (sectionOfIsPullback sq hs₀)) F.zero
      (sectionOfIsPullback sq hs₀ ≫ g') := by
    rw [sectionOfIsPullback_g']
    exact hout
  have h₁ := restrictSupportedClass_comp_tateShift Λ g s₀ _ (sectionOfIsPullback_g' sq hs₀)
    F.zero (pullback.snd F.zero s₀) _ (pullback.fst F.zero s₀)
    (IsPullback.of_hasPullback F.zero s₀) g₁ hg₁ _ hout' (F.thomClass Λ aT)
  have h₂ := restrictSupportedClass_comp_tateShift Λ (sectionOfIsPullback sq hs₀) g' _ rfl
    F.zero (F.ofIsPullback sq).zero _ g (F.isPullback_zero_ofIsPullback sq) _
    (IsPullback.of_hasPullback (F.ofIsPullback sq).zero (sectionOfIsPullback sq hs₀)) _ hout'
    (F.thomClass Λ aT)
  rw [localizedTopChern, ← h₁, localizedTopChern,
    ← F.restrictSupportedClass_thomClass_ofIsPullback (sq := sq) (Λ := Λ) (aT := aT) (aS' := aS'),
    ← h₂]

end BaseChange


end VectorBundle

end AlgebraicGeometry
