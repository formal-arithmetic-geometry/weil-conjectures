/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Canonical
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Hyperplane
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistBundle
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineChern
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion
public import WeilConjectures.EtaleCohomology.Purity.Smooth.VectorBundle
public import WeilConjectures.EtaleCohomology.Purity.Smooth.TopChernClass

/-!
# The hyperplane class of projective space and the projective-space formula

The coordinate hyperplane `H = V(T_∗) ⊆ ℙ(Option n; S)`, the image of the hyperplane embedding
(`AlgebraicGeometry.ProjectiveSpace.hyperplane`), is cut out on the chart `D₊(Tᵢ)` by the single
function `T_∗ / Tᵢ` (`AlgebraicGeometry.ProjectiveSpace.hyperplaneFrame`). Its Kummer class
`[H] ∈ H²_H(ℙ, Λ(1))` is the class with supports restricting to `∂κ(T_∗ / Tᵢ)` on every chart
(`AlgebraicGeometry.Etale.IsHyperplaneClass`), and forgetting supports gives the first Chern class
`h = c₁(𝒪(1))`. With its cup powers `hᵃ` (`AlgebraicGeometry.Etale.chernPow`), the projective-space
formula says that

`(1, h, …, hⁿ) : ⊕ₐ Λ_S(-a)[-2a] ⟶ Rq_* Λ_{ℙⁿ_S}`

is an isomorphism (`AlgebraicGeometry.Etale.isIso_projectiveFormulaMap`, the case of a
trivial bundle of `thm-pur-projective-bundle-formula`; stated, not proved).

The hyperplane class exists and is unique (`AlgebraicGeometry.Etale.hyperplaneClass`), and its
adjoint `Λ ⟶ RH^! Λ(1)[2]` is an isomorphism
(`AlgebraicGeometry.Etale.isIso_supportedClassMap_hyperplaneClass`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace ProjectiveSpace

variable (n : Type u) (S : Scheme.{u})

lemma image_extraCoord_eq_range (i : n) :
    (standardOpenIso (Option n) S (some i)).hom.appTop '' {extraCoord n S i} =
      Set.range (fun _ : Fin 1 ↦ (standardOpenIso (Option n) S (some i)).hom.appTop
        (extraCoord n S i)) := by
  rw [Set.image_singleton, Set.range_const]

/-- The hyperplane over the chart `D₊(Tᵢ)`, as the zero locus of `T_∗ / Tᵢ`, maps to `ℙ(n; S)`. -/
noncomputable def hyperplaneFrameToZ (i : n) :
    (standardOpen (Option n) S (some i)).toScheme.zeroLocusSubscheme
        (Set.range (fun _ : Fin 1 ↦ (standardOpenIso (Option n) S (some i)).hom.appTop
          (extraCoord n S i))) ⟶ ℙ(n; S) :=
  (standardOpenIso (Option n) S (some i)).hom.zeroLocusSubschemeMap _ _
      (image_extraCoord_eq_range n S i) ≫
    (hyperplaneChartIso n S i).inv ≫ (hyperplanePreimageIso n S i).hom ≫
      (hyperplane n S ⁻¹ᵁ standardOpen (Option n) S (some i)).ι

lemma isPullback_hyperplaneFrame (i : n) :
    IsPullback (hyperplaneFrameToZ n S i)
      ((standardOpen (Option n) S (some i)).toScheme.zeroLocusSubschemeι
        (Set.range (fun _ : Fin 1 ↦ (standardOpenIso (Option n) S (some i)).hom.appTop
          (extraCoord n S i))))
      (hyperplane n S) (standardOpen (Option n) S (some i)).ι := by
  have P₁ := isPullback_zeroLocusSubschemeι (standardOpenIso (Option n) S (some i)).hom
    {extraCoord n S i} _ (image_extraCoord_eq_range n S i)
  have P₂ : IsPullback ((hyperplaneChartIso n S i).inv ≫ (hyperplanePreimageIso n S i).hom)
      (𝔸({j : Option n // j ≠ some i}; S).zeroLocusSubschemeι {extraCoord n S i})
      (hyperplane n S ∣_ standardOpen (Option n) S (some i))
      (standardOpenIso (Option n) S (some i)).inv :=
    IsPullback.of_horiz_isIso ⟨by
      rw [Category.assoc, hyperplanePreimageIso_hom_morphismRestrict, ← hyperplaneChartIso_hom_ι,
        Category.assoc, Iso.inv_hom_id_assoc]⟩
  have P₃ := (isPullback_morphismRestrict (hyperplane n S)
    (standardOpen (Option n) S (some i))).flip
  have h := (P₁.paste_horiz P₂).paste_horiz P₃
  rw [Iso.hom_inv_id, Category.id_comp] at h
  simpa only [hyperplaneFrameToZ, Category.assoc] using h

/-- The frame of the hyperplane on the chart `D₊(Tᵢ)`: the function `T_∗ / Tᵢ`. -/
noncomputable def hyperplaneFrame (i : n) : (hyperplane n S).EtaleFrame 1 where
  U := (standardOpen (Option n) S (some i)).toScheme
  e := (standardOpen (Option n) S (some i)).ι
  etale := inferInstance
  f _ := (standardOpenIso (Option n) S (some i)).hom.appTop (extraCoord n S i)
  toZ := hyperplaneFrameToZ n S i
  isPullback := isPullback_hyperplaneFrame n S i

/-- The zero scheme of the coordinate section `[x] ↦ [x : x_∗]` of `𝒪(1)` on `ℙ(Option m; S)` is
the hyperplane `ℙ(m; S)`: the square formed with the hyperplane `ℙ(Option m; S) ⊆
ℙ(Option (Option m); S)` is cartesian.

Proof: `AlgebraicGeometry.isPullback_of_iSup_opensRange_eq_top` over the cover of
`ℙ(Option m; S)` by the `D₊(a)`, with `hchart` from `isPullback_morphismRestrict`. For
`a = some k`, factor `D₊(some k) ⟶ ℙ(Option (Option m); S)` through `D₊(some (some k))`, paste
the frame square `hyperplaneFrame (Option m) S (some k)` with the pull-back of its zero locus
(`isPullback_zeroLocusSubschemeι`), whose function is `x_∗ / x_k`, and identify that zero locus
with `ℙ(m) ∩ D₊(k)` using `hyperplaneFrame m S k`. For `a = none` both sides are empty
(`hyperplane_preimage_standardOpen_none`, and `D₊(∗)` maps into `D₊(∗)`). -/
lemma isPullback_hyperplane_twistBundleSectionAux {m : Type u} :
    IsPullback (hyperplane m S) (hyperplane m S) (twistBundleSectionAux (Option m) S none)
      (hyperplane (Option m) S) := by
  refine isPullback_of_iSup_opensRange_eq_top (hyperplane_comp_twistBundleSectionAux_none S)
    (m := fun a ↦ (standardOpen (Option m) S a).ι)
    (n := fun a ↦ (hyperplane m S ⁻¹ᵁ standardOpen (Option m) S a).ι)
    (k := fun a ↦ hyperplane m S ∣_ standardOpen (Option m) S a) ?_
    (fun a ↦ isPullback_morphismRestrict _ _) fun a ↦ ?_
  · simp only [Scheme.Opens.opensRange_ι]
    exact iSup_standardOpen (Option m) S
  cases a with
  | none =>
    have hX : IsEmpty (hyperplane m S ⁻¹ᵁ standardOpen (Option m) S none).toScheme :=
      ⟨fun x ↦ by
        have h : x.1 ∈ (⊥ : ℙ(m; S).Opens) := by
          rw [← hyperplane_preimage_standardOpen_none m S]
          exact x.2
        exact h⟩
    have hσ : twistBundleSectionAux (Option m) S none ⁻¹ᵁ
        standardOpen (Option (Option m)) S none = standardOpen (Option m) S none := by
      rw [twistBundleSectionAux, Scheme.CoordinateCover.preimage_hom_standardOpen]
      exact nonvanishing_coord _ _
    let σ' : (standardOpen (Option m) S none).toScheme ⟶ ℙ(Option (Option m); S) :=
      (standardOpen (Option m) S none).ι ≫ twistBundleSectionAux (Option m) S none
    let ι' : ℙ(Option m; S) ⟶ ℙ(Option (Option m); S) := hyperplane (Option m) S
    have hP : IsEmpty (Limits.pullback σ' ι' : Scheme.{u}) :=
      ⟨fun (z : (Limits.pullback σ' ι' : Scheme.{u})) ↦ by
        have hy : (standardOpen (Option m) S none).ι.base (Limits.pullback.fst σ' ι' z) ∈
            twistBundleSectionAux (Option m) S none ⁻¹ᵁ
              standardOpen (Option (Option m)) S none := by
          rw [hσ]
          exact (Limits.pullback.fst σ' ι' z).2
        have h2 : Limits.pullback.snd σ' ι' z ∈
            hyperplane (Option m) S ⁻¹ᵁ standardOpen (Option (Option m)) S none := by
          change ((Limits.pullback.snd σ' ι' ≫ ι').base z) ∈ standardOpen (Option (Option m)) S none
          rw [← Limits.pullback.condition, Scheme.Hom.comp_apply]
          exact hy
        rw [hyperplane_preimage_standardOpen_none] at h2
        exact h2⟩
    exact IsPullback.of_iso_pullback ⟨isInitialOfIsEmpty.hom_ext _ _⟩
      (isInitialOfIsEmpty.uniqueUpToIso isInitialOfIsEmpty) (isInitialOfIsEmpty.hom_ext _ _)
      (isInitialOfIsEmpty.hom_ext _ _)
  | some k =>
    have hb₀ : Set.range ((standardOpen (Option m) S (some k)).ι ≫
        twistBundleSectionAux (Option m) S none).base ⊆
        Set.range (standardOpen (Option (Option m)) S (some (some k))).ι.base := by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      have hx : x.1 ∈ twistBundleSectionAux (Option m) S none ⁻¹ᵁ
          standardOpen (Option (Option m)) S (some (some k)) := by
        rw [twistBundleSectionAux_preimage_standardOpen_some]
        exact x.2
      exact hx
    let b := IsOpenImmersion.lift _ _ hb₀
    have hbι : b ≫ (standardOpen (Option (Option m)) S (some (some k))).ι =
        (standardOpen (Option m) S (some k)).ι ≫ twistBundleSectionAux (Option m) S none :=
      IsOpenImmersion.lift_fac _ _ _
    have hv : b.appTop ((standardOpenIso (Option (Option m)) S (some (some k))).hom.appTop
        (extraCoord (Option m) S (some k))) =
        (standardOpenIso (Option m) S (some k)).hom.appTop (extraCoord m S k) := by
      change b.appTop ((standardOpenIso _ S _).hom.appTop (AffineSpace.coord S ⟨none, by simp⟩)) =
        (standardOpenIso _ S _).hom.appTop (AffineSpace.coord S ⟨none, by simp⟩)
      rw [standardOpenIso_hom_appTop_coord, standardOpenIso_hom_appTop_coord]
      have e₀ : (standardOpen (Option (Option m)) S (some (some k))).topIso.inv =
          (standardOpen (Option (Option m)) S (some (some k))).ι.appLE
            (standardOpen (Option (Option m)) S (some (some k))) ⊤
            (Scheme.Opens.ι_preimage_self _).ge := by
        rw [Scheme.Opens.ι_appLE]
        rfl
      have e₂ : b.appTop = b.appLE ⊤ ⊤ le_top := by
        rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
        rfl
      have hh : (standardOpen (Option m) S (some k)).ι ≫ twistBundleSectionAux (Option m) S none =
          homOfSections ((standardOpen (Option m) S (some k)).ι ≫ ℙ(Option m; S) ↘ S)
            (fun a ↦ (standardOpen (Option m) S (some k)).topIso.inv
              ((twistBundleSectionSections (Option m) S none a).s (some k)))
            (Scheme.CoordinateCover.span_topIso_inv _
              (span_twistBundleSectionSections (Option m) S none) (some k)) :=
        Scheme.CoordinateCover.ι_hom (𝒟 := standardCoordinateCover (Option m) S) _ _ _ _
      rw [e₀, e₂, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, appLE_eq_of_eq hbι,
        appLE_eq_of_eq hh]
      exact (homOfSections_appLE_coordRatio (S := S) _
        (fun a ↦ (standardOpen (Option m) S (some k)).topIso.inv
          ((twistBundleSectionSections (Option m) S none a).s (some k)))
        (Scheme.CoordinateCover.span_topIso_inv _
          (span_twistBundleSectionSections (Option m) S none) (some k))
        (twistBundleSectionSections_some_s_self (Option m) S none (some k)) none _).trans rfl
    have hz := isPullback_zeroLocusSubschemeι b
      (Set.range fun _ : Fin 1 ↦ (standardOpenIso (Option (Option m)) S (some (some k))).hom.appTop
        (extraCoord (Option m) S (some k)))
      (Set.range fun _ : Fin 1 ↦ (standardOpenIso (Option m) S (some k)).hom.appTop
        (extraCoord m S k))
      (by rw [← Set.range_comp]; exact congrArg Set.range (funext fun _ ↦ hv))
    have P₁ := hz.paste_horiz (isPullback_hyperplaneFrame (Option m) S (some k))
    have hG := isPullback_hyperplaneFrame m S k
    let e := hG.isoIsPullback _ _
      (isPullback_morphismRestrict (hyperplane m S) (standardOpen (Option m) S (some k))).flip
    refine P₁.flip.of_iso e (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [e]
    · have h₁ := (isPullback_hyperplaneFrame (Option m) S (some k)).w
      have h₂ := hz.w
      have h₃ := hG.w
      rw [Iso.refl_hom, Category.comp_id, ← Category.assoc, IsPullback.isoIsPullback_hom_fst,
        ← cancel_mono (hyperplane (Option m) S)]
      simp only [Category.assoc]
      rw [h₁, ← hyperplane_comp_twistBundleSectionAux_none, reassoc_of% h₃, reassoc_of% h₂, hbι]
    · simp [hbι]
    · simp

end ProjectiveSpace

namespace Etale

open ProjectiveSpace

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ] (n : Type u)
  (S : Scheme.{u}) [HasInvertibleExponent Λ S]

instance (n : Type u) (S : Scheme.{u}) [HasInvertibleExponent Λ S] :
    HasInvertibleExponent Λ ℙ(n; S) :=
  .of_hom (ℙ(n; S) ↘ S)

/-- Blueprint `lem-pur-divisor-class`: Divisor classes

The *Kummer class of the coordinate hyperplane* `[H] ∈ H²_H(ℙ(Option n; S), Λ(1))`: a class with
supports in the hyperplane `H = V(T_∗)` is a hyperplane class if it restricts on every chart
`D₊(Tᵢ)` to the Kummer boundary `∂κ(T_∗ / Tᵢ)` of the local equation of `H`
(`AlgebraicGeometry.ProjectiveSpace.hyperplaneFrame`). -/
def IsHyperplaneClass
    (γ : constantComplex Λ ℙ(Option n; S) ⟶ (R(hyperplane n S)_![ModuleCat.{u + 1} Λ]).obj
      ((R(hyperplane n S)^![ModuleCat.{u + 1} Λ]).obj
        ((tateObject Λ ℙ(Option n; S) ((1 : ℕ) : ℤ))⟦2 * ((1 : ℕ) : ℤ)⟧))) : Prop :=
  ∀ i, frameRestriction Λ (hyperplaneFrame n S i) γ = frameClass Λ (hyperplaneFrame n S i)

variable {Λ n S} in
/-- The first Chern class `h = c₁(𝒪(1)) ∈ H²(ℙ(Option n; S), Λ(1))`: a hyperplane class with
supports forgotten. -/
noncomputable def hyperplaneChernClass
    (γ : constantComplex Λ ℙ(Option n; S) ⟶ (R(hyperplane n S)_![ModuleCat.{u + 1} Λ]).obj
      ((R(hyperplane n S)^![ModuleCat.{u + 1} Λ]).obj
        ((tateObject Λ ℙ(Option n; S) ((1 : ℕ) : ℤ))⟦2 * ((1 : ℕ) : ℤ)⟧))) :
    constantComplex Λ ℙ(Option n; S) ⟶ (tateObject Λ ℙ(Option n; S) 1)⟦2 * (1 : ℤ)⟧ :=
  γ ≫ (rightDerivedUpperShriekAdjunction (ModuleCat.{u + 1} Λ) (hyperplane n S)).counit.app _

section Powers

variable {Λ} {X : Scheme.{u}} [HasInvertibleExponent Λ X]

/-- The isomorphism `Λ_X(m + -m)[2(m + -m)] ≅ Λ_X`. -/
noncomputable def tateObjectShiftAddNegIso (m : ℤ) :
    (tateObject Λ X (m + -m))⟦2 * (m + -m)⟧ ≅ constantComplex Λ X :=
  (shiftFunctorZero' _ (2 * (m + -m)) (by ring)).app _ ≪≫
    eqToIso (by simp [tateObject]) ≪≫ HasTateTwist.twistObjectZeroIso X

/-- The unit class `Λ_X ≅ Λ_X(0)[0]`. -/
noncomputable def tateObjectShiftZeroIso' :
    constantComplex Λ X ≅ (tateObject Λ X 0)⟦2 * (0 : ℤ)⟧ :=
  (HasTateTwist.twistObjectZeroIso X).symm ≪≫
    (shiftFunctorZero' _ (2 * (0 : ℤ)) (by ring)).symm.app _

/-- The cup powers `hᵃ ∈ H^{2a}(X, Λ(a))` of a class `h ∈ H²(X, Λ(1))`: `h⁰ = 1` and
`hᵃ⁺¹ = hᵃ ∪ h`. -/
noncomputable def chernPow (h : constantComplex Λ X ⟶ (tateObject Λ X 1)⟦2 * (1 : ℤ)⟧) :
    (a : ℕ) → (constantComplex Λ X ⟶ (tateObject Λ X a)⟦2 * (a : ℤ)⟧)
  | 0 => (tateObjectShiftZeroIso' (Λ := Λ)).hom
  | a + 1 => constantComplexDiagonal Λ X ≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).map (chernPow h a)).app _ ≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj _).map h ≫
      (shiftTateObjectAddIso Λ X a 1).hom ≫ eqToHom (by push_cast; rfl)

end Powers

variable {Λ n S}

/-- The component `Λ_S(-a)[-2a] ⟶ Rq_* Λ_{ℙ}` of the projective-space formula: the adjoint of
`Lq^*(Λ_S(-a)[-2a]) ≅ Λ ⊗ Λ(-a)[-2a] ⟶ Λ(a)[2a] ⊗ Λ(-a)[-2a] ≅ Λ`, the first map being `hᵃ ⊗ 1`. -/
noncomputable def chernPowMap {P : Scheme.{u}} (q : P ⟶ S) [HasInvertibleExponent Λ P]
    (h : constantComplex Λ P ⟶ (tateObject Λ P 1)⟦2 * (1 : ℤ)⟧) (a : ℕ) :
    (tateObject Λ S (-(a : ℤ)))⟦2 * (-(a : ℤ))⟧ ⟶
      (R((q)_*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ P) :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).homEquiv _ _
    ((leftDerivedUpperStarTateShiftIso Λ q (-(a : ℤ))).hom ≫
      (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) P _).inv ≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) P).map (chernPow h a)).app _ ≫
      (shiftTateObjectAddIso Λ P a (-(a : ℤ))).hom ≫
      (tateObjectShiftAddNegIso (a : ℤ)).hom)

/-- The map `(1, h, …, hʳ) : ⊕_{a ≤ r} Λ_S(-a)[-2a] ⟶ Rq_* Λ_P` of the projective bundle formula,
for a class `h ∈ H²(P, Λ(1))`. -/
noncomputable def projectiveFormulaMap {P : Scheme.{u}} (q : P ⟶ S) [HasInvertibleExponent Λ P]
    (h : constantComplex Λ P ⟶ (tateObject Λ P 1)⟦2 * (1 : ℤ)⟧) (r : ℕ) :
    (⨁ fun a : Fin (r + 1) ↦ (tateObject Λ S (-(a : ℤ)))⟦2 * (-(a : ℤ))⟧) ⟶
      (R((q)_*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ P) :=
  biproduct.desc fun a ↦ chernPowMap q h a

omit [Finite Λ] in
/-- The projective-space formula in relative dimension `0`: for an isomorphism `q`, the map
`Λ_S ⟶ Rq_* Λ_P` is an isomorphism. -/
lemma isIso_projectiveFormulaMap_zero {P : Scheme.{u}} (q : P ⟶ S) [IsIso q]
    [HasInvertibleExponent Λ P] (h : constantComplex Λ P ⟶ (tateObject Λ P 1)⟦2 * (1 : ℤ)⟧) :
    IsIso (projectiveFormulaMap q h 0) := by
  let F : Fin (0 + 1) → _ := fun a ↦ (tateObject Λ S (-(a : ℤ)))⟦2 * (-(a : ℤ))⟧
  have hdesc : projectiveFormulaMap q h 0 =
      biproduct.π F 0 ≫
        chernPowMap q h 0 := by
    refine biproduct.hom_ext' _ _ fun j ↦ ?_
    obtain rfl : j = 0 := Subsingleton.elim (α := Fin 1) _ _
    simp only [projectiveFormulaMap, biproduct.ι_desc, F, biproduct.ι_π_self_assoc]
    rfl
  have hπ : IsIso (biproduct.π F 0) := by
    refine ⟨⟨biproduct.ι F 0, ?_, by simp⟩⟩
    refine biproduct.hom_ext' _ _ fun j ↦ ?_
    obtain rfl : j = 0 := Subsingleton.elim (α := Fin 1) _ _
    simp
  have hu : IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) q).unit.app
      ((tateObject Λ S (-((0 : ℕ) : ℤ)))⟦2 * (-((0 : ℕ) : ℤ))⟧)) := by
    have hid : IsIso ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 S)).unit.app
        ((tateObject Λ S (-((0 : ℕ) : ℤ)))⟦2 * (-((0 : ℕ) : ℤ))⟧)) := by
      obtain ⟨e⟩ := nonempty_leftDerivedUpperStar_id_iso Λ S (𝟙 S) rfl
      have : (L((𝟙 S)^*[ModuleCat.{u + 1} Λ])).Full := Functor.Full.of_iso e.symm
      have : (L((𝟙 S)^*[ModuleCat.{u + 1} Λ])).Faithful := Functor.Faithful.of_iso e.symm
      infer_instance
    have := isIso_unit_app_comp_of_isIso Λ q (𝟙 S) _ hid
    rwa [Category.comp_id] at this
  rw [hdesc, chernPowMap, Adjunction.homEquiv_unit]
  simp only [chernPow]
  infer_instance

omit [Finite Λ] in
lemma isIso_projectiveFormulaMap_of_eq_zero {P : Scheme.{u}} (q : P ⟶ S) [IsIso q]
    [HasInvertibleExponent Λ P] (h : constantComplex Λ P ⟶ (tateObject Λ P 1)⟦2 * (1 : ℤ)⟧)
    (r : ℕ) (hr : r = 0) : IsIso (projectiveFormulaMap q h r) := by
  subst hr
  exact isIso_projectiveFormulaMap_zero q h

variable [HasKummerClass.IsNormalized Λ] {k : Type u} [Field k] (aS : S ⟶ Spec (.of k))
  [IsSeparated aS] [LocallyOfFiniteType aS]

attribute [local instance] HasInvertibleExponent.opens

/-- The coordinates of `{j : Option n // j ≠ some i}` are those of `{k // k ≠ i}` and `∗`. -/
def chartIndexEquiv (i : n) :
    {k : n // k ≠ i} ⊕ ULift.{u} (Fin 1) ≃ {j : Option n // j ≠ some i} where
  toFun
    | .inl k => ⟨some k.1, by simpa using k.2⟩
    | .inr _ => ⟨none, by simp⟩
  invFun
    | ⟨none, _⟩ => .inr ⟨0⟩
    | ⟨some k, hk⟩ => .inl ⟨k, fun h ↦ hk (by rw [h])⟩
  left_inv
    | .inl _ => rfl
    | .inr ⟨a⟩ => by
      obtain rfl : a = 0 := Subsingleton.elim _ _
      rfl
  right_inv
    | ⟨none, _⟩ => rfl
    | ⟨some _, _⟩ => rfl

include aS in
/-- The class of a frame of the hyperplane generates: its adjoint is an isomorphism. On the
chart `D₊(Tᵢ) ≅ 𝔸¹_{𝔸({k // k ≠ i})}` it is the Kummer boundary of the coordinate of the affine
line (`AlgebraicGeometry.Etale.isIso_supportedClassMap_kummerBoundaryProduct_coord`). -/
lemma isIso_supportedClassMap_hyperplaneFrame [Finite n] (i : n) :
    IsIso (supportedClassMap Λ ((hyperplaneFrame n S i).U.zeroLocusSubschemeι
      (Set.range (hyperplaneFrame n S i).f)) (frameClass Λ (hyperplaneFrame n S i))) := by
  have hmodel := isIso_supportedClassMap_kummerBoundaryProduct_coord Λ 1 𝔸({k : n // k ≠ i}; S)
    (𝔸({k : n // k ≠ i}; S) ↘ S ≫ aS)
  let θ := AffineSpace.reindex (chartIndexEquiv i) S ≫ (AffineSpace.sumIso S).hom
  have hθ : IsIso θ := by
    have : IsIso (AffineSpace.reindex (chartIndexEquiv i) S) :=
      (AffineSpace.reindexIso S (chartIndexEquiv i)).isIso_hom
    infer_instance
  have h₁ := isIso_supportedClassMap_kummerBoundaryProduct_of_etale Λ θ
    (fun a : Fin 1 ↦ AffineSpace.coord 𝔸({k : n // k ≠ i}; S) (ULift.up a))
    (fun _ ↦ extraCoord n S i)
    (fun a ↦ by
      obtain rfl : a = 0 := Subsingleton.elim _ _
      rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, AffineSpace.sumIso_hom,
        AffineSpace.sumHom, AffineSpace.homOfVector_appTop_coord, Function.comp_apply,
        AffineSpace.reindex_appTop_coord]
      rfl) hmodel
  exact isIso_supportedClassMap_kummerBoundaryProduct_of_etale Λ
    (standardOpenIso (Option n) S (some i)).hom _ (hyperplaneFrame n S i).f (fun _ ↦ rfl) h₁

lemma disjoint_range_hyperplane :
    Disjoint (Set.range (hyperplane n S).base)
      (Set.range (standardOpen (Option n) S none).ι.base) := by
  rw [Set.disjoint_left]
  rintro _ ⟨y, rfl⟩ hy
  rw [Scheme.Opens.range_ι] at hy
  have h : y ∈ hyperplane n S ⁻¹ᵁ standardOpen (Option n) S none := hy
  rw [hyperplane_preimage_standardOpen_none] at h
  exact h

include aS in
/-- Classes with supports in the hyperplane are sections of a sheaf: `RH_! RH^! Λ(1)[2]` has no
cohomology outside degree zero. -/
theorem isZero_homology_hyperplaneTarget [Finite n] (m : ℤ) (hm : m ≠ 0) :
    IsZero ((_root_.DerivedCategory.homologyFunctor _ m).obj
      ((R(hyperplane n S)_![ModuleCat.{u + 1} Λ]).obj
        ((R(hyperplane n S)^![ModuleCat.{u + 1} Λ]).obj
          ((tateObject Λ ℙ(Option n; S) ((1 : ℕ) : ℤ))⟦2 * ((1 : ℕ) : ℤ)⟧)))) := by
  refine isZero_homology_of_jointlySurjective Λ
    (fun a : Option n ↦ (standardOpen (Option n) S a).ι) (fun x ↦ ?_) _ m fun a ↦ ?_
  · obtain ⟨a, ha⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_standardOpen (Option n) S).ge (Set.mem_univ x))
    exact ⟨a, ⟨x, ha⟩, rfl⟩
  cases a with
  | none =>
    exact Functor.map_isZero _ (isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint
      (ModuleCat.{u + 1} Λ) (hyperplane n S) (standardOpen (Option n) S none).ι
      disjoint_range_hyperplane _ subset_rfl _)
  | some i =>
    have : IsOpenImmersion (hyperplaneFrame n S i).e :=
      inferInstanceAs (IsOpenImmersion (standardOpen (Option n) S (some i)).ι)
    have hψ := isIso_supportedRestriction_of_isOpenImmersion (ModuleCat.{u + 1} Λ)
      (hyperplaneFrame n S i).e (hyperplane n S) _ (hyperplaneFrame n S i).toZ
      (hyperplaneFrame n S i).isPullback _ _
      (leftDerivedUpperStarTateShiftIso Λ (hyperplaneFrame n S i).e 1)
    have hφ := isIso_supportedClassMap_hyperplaneFrame (Λ := Λ) aS i
    have : (constantComplex Λ ((hyperplaneFrame n S i).U.zeroLocusSubscheme
        (Set.range (hyperplaneFrame n S i).f))).IsGE 0 :=
      (_root_.DerivedCategory.isGE_iff _ 0).2 fun n hn ↦
        isZero_homology_constantComplex Λ _ n hn.ne
    have : (constantComplex Λ ((hyperplaneFrame n S i).U.zeroLocusSubscheme
        (Set.range (hyperplaneFrame n S i).f))).IsLE 0 :=
      (_root_.DerivedCategory.isLE_iff _ 0).2 fun n hn ↦
        isZero_homology_constantComplex Λ _ n hn.ne'
    exact (isZero_homology_rightDerivedLowerShriek_of_isClosedImmersion Λ _ _ m
      hm).of_iso
      ((_root_.DerivedCategory.homologyFunctor _ m).mapIso (asIso (supportedRestriction _ _ _ _ _
        (hyperplaneFrame n S i).isPullback _ _
          (leftDerivedUpperStarTateShiftIso Λ (hyperplaneFrame n S i).e 1)) ≪≫
          (R(_)_![ModuleCat.{u + 1} Λ]).mapIso (asIso (supportedClassMap Λ _
            (frameClass Λ (hyperplaneFrame n S i)))).symm))

omit [HasInvertibleExponent Λ S] [HasKummerClass.IsNormalized Λ] in
/-- On the overlap of two charts, the local equations `T_∗ / Tᵢ` and `T_∗ / Tⱼ` of the hyperplane
differ by the unit `Tᵢ / Tⱼ`. -/
lemma exists_unit_hyperplaneFrame (i j : n) {W : Scheme.{u}}
    (a : W ⟶ (standardOpen (Option n) S (some i)).toScheme)
    (b : W ⟶ (standardOpen (Option n) S (some j)).toScheme)
    (h : a ≫ (standardOpen (Option n) S (some i)).ι = b ≫ (standardOpen (Option n) S (some j)).ι) :
    ∃ v : Γ(W, ⊤)ˣ, b.appTop ((hyperplaneFrame n S j).f 0) =
      v * a.appTop ((hyperplaneFrame n S i).f 0) := by
  have hr : Set.range (a ≫ (standardOpen (Option n) S (some i)).ι).base ⊆
      Set.range (standardOpen (Option n) S (some i) ⊓
        standardOpen (Option n) S (some j)).ι.base := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine ⟨?_, ?_⟩
    · rw [Scheme.Hom.comp_apply]
      exact (a.base y).2
    · rw [h, Scheme.Hom.comp_apply]
      exact (b.base y).2
  obtain ⟨c, hca, hcb⟩ : ∃ c : W ⟶ (standardOpen (Option n) S (some i) ⊓
      standardOpen (Option n) S (some j)).toScheme,
      c ≫ ℙ(Option n; S).homOfLE inf_le_left = a ∧ c ≫ ℙ(Option n; S).homOfLE inf_le_right = b := by
    have hc := IsOpenImmersion.lift_fac _ _ hr
    refine ⟨IsOpenImmersion.lift _ _ hr, ?_, ?_⟩
    · rw [← cancel_mono (standardOpen (Option n) S (some i)).ι, Category.assoc,
        Scheme.homOfLE_ι, hc]
    · rw [← cancel_mono (standardOpen (Option n) S (some j)).ι, Category.assoc,
        Scheme.homOfLE_ι, hc, h]
  clear hr h
  let ψ : Γ(ℙ(Option n; S), standardOpen (Option n) S (some i) ⊓
      standardOpen (Option n) S (some j)) →+* Γ(W, ⊤) :=
    c.appTop.hom.comp (standardOpen (Option n) S (some i) ⊓
      standardOpen (Option n) S (some j)).topIso.inv.hom
  have key : ∀ (k : n) (hk : standardOpen (Option n) S (some i) ⊓
      standardOpen (Option n) S (some j) ≤ standardOpen (Option n) S (some k))
      (e : W ⟶ (standardOpen (Option n) S (some k)).toScheme)
      (_ : c ≫ ℙ(Option n; S).homOfLE hk = e),
      e.appTop ((hyperplaneFrame n S k).f 0) =
        ψ (ℙ(Option n; S).presheaf.map (homOfLE hk).op
          (coordRatio (Option n) S (some k) none)) := by
    rintro k hk _ rfl
    change (c ≫ _).appTop ((standardOpenIso (Option n) S (some k)).hom.appTop
      (AffineSpace.coord S ⟨none, by simp⟩)) = _
    rw [standardOpenIso_hom_appTop_coord, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      Scheme.homOfLE_appTop_topIso_inv]
    rfl
  refine ⟨Units.map ψ.toMonoidHom (ratioUnit (Option n) S (some i) (some j)), ?_⟩
  rw [key j inf_le_right b hcb, key i inf_le_left a hca,
    map_coordRatio_eq_mul (S := S) (n := Option n) (W := standardOpen (Option n) S (some i) ⊓
      standardOpen (Option n) S (some j)) inf_le_left inf_le_right none,
    map_coordRatio_eq_ratioUnit_inv]
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, map_mul]
  rw [mul_left_comm, ← map_mul, Units.mul_inv, map_one, mul_one]

variable (Λ n) in
include aS in
/-- Blueprint `lem-pur-divisor-class`: Divisor classes

*Existence of the hyperplane class.* The Kummer classes `∂κ(T_∗ / Tᵢ)` of the local equations of
the coordinate hyperplane glue to a class with supports in the hyperplane.
The gluing is that of `AlgebraicGeometry.VectorBundle.exists_thomClass`, the frames on
`D₊(Tᵢ) ∩ D₊(Tⱼ)` differing by the unit `Tᵢ / Tⱼ` (`exists_unit_hyperplaneFrame`). -/
theorem exists_isHyperplaneClass [Finite n] :
    ∃ γ, IsHyperplaneClass Λ n S γ := by
  set K := (R(hyperplane n S)_![ModuleCat.{u + 1} Λ]).obj
    ((R(hyperplane n S)^![ModuleCat.{u + 1} Λ]).obj
      ((tateObject Λ ℙ(Option n; S) ((1 : ℕ) : ℤ))⟦2 * ((1 : ℕ) : ℤ)⟧)) with hK
  have hKz := isZero_homology_hyperplaneTarget (Λ := Λ) (n := n) aS
  have : K.IsGE 0 := (_root_.DerivedCategory.isGE_iff K 0).2 fun m hm ↦ hKz m hm.ne
  have : K.IsLE 0 := (_root_.DerivedCategory.isLE_iff K 0).2 fun m hm ↦ hKz m hm.ne'
  obtain ⟨G, ⟨eM⟩⟩ := _root_.DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K 0
  let e : ∀ j : Option n, (standardOpen (Option n) S j).toScheme ⟶ ℙ(Option n; S) :=
    fun j ↦ (standardOpen (Option n) S j).ι
  have hcov : ∀ x : ℙ(Option n; S), ∃ j, x ∈ Set.range (e j).base := by
    intro x
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_standardOpen (Option n) S).ge (Set.mem_univ x))
    exact ⟨j, ⟨x, hj⟩, rfl⟩
  have hΨ : ∀ i, IsIso (supportedRestriction (ModuleCat.{u + 1} Λ) (hyperplaneFrame n S i).e
      (hyperplane n S) _ (hyperplaneFrame n S i).toZ (hyperplaneFrame n S i).isPullback _ _
      (leftDerivedUpperStarTateShiftIso Λ (hyperplaneFrame n S i).e 1)) := fun i ↦ by
    have : IsOpenImmersion (hyperplaneFrame n S i).e :=
      inferInstanceAs (IsOpenImmersion (standardOpen (Option n) S (some i)).ι)
    exact isIso_supportedRestriction_of_isOpenImmersion _ _ _ _ _ _ _ _ _
  let δ : ∀ j, (L((e j)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ ℙ(Option n; S)) ⟶
      (L((e j)^*[ModuleCat.{u + 1} Λ])).obj K := fun j ↦ match j with
    | none => 0
    | some i => (leftDerivedUpperStarConstantComplexIso Λ (hyperplaneFrame n S i).e).hom ≫
        frameClass Λ (hyperplaneFrame n S i) ≫
        inv (supportedRestriction (ModuleCat.{u + 1} Λ) (hyperplaneFrame n S i).e
          (hyperplane n S) _ (hyperplaneFrame n S i).toZ (hyperplaneFrame n S i).isPullback _ _
          (leftDerivedUpperStarTateShiftIso Λ (hyperplaneFrame n S i).e 1))
  have hδ : ∀ i, δ (some i) ≫ supportedRestriction (ModuleCat.{u + 1} Λ)
      (hyperplaneFrame n S i).e (hyperplane n S) _ (hyperplaneFrame n S i).toZ
        (hyperplaneFrame n S i).isPullback _ _
        (leftDerivedUpperStarTateShiftIso Λ (hyperplaneFrame n S i).e 1) =
        (leftDerivedUpperStarConstantComplexIso Λ (hyperplaneFrame n S i).e).hom ≫
          frameClass Λ (hyperplaneFrame n S i) := by
    intro i
    simp [δ]
  have hzero : ∀ {W : Scheme.{u}} (w : W ⟶ ℙ(Option n; S)),
      Set.range w.base ⊆ Set.range (standardOpen (Option n) S none).ι.base →
      IsZero ((L((w)^*[ModuleCat.{u + 1} Λ])).obj K) :=
    fun w hw ↦ isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint _
      (hyperplane n S) (standardOpen (Option n) S none).ι disjoint_range_hyperplane w hw _
  obtain ⟨γ, hγ⟩ := exists_hom_of_isOpenImmersion_cover
    (constantComplexIsoSingleFunctor Λ ℙ(Option n; S)) eM e hcov δ (by
    rintro (_ | i) (_ | j) W a b _ _ h
    · exact (hzero _ (by rintro _ ⟨y, rfl⟩; exact ⟨a y, rfl⟩)).eq_of_tgt _ _
    · exact (hzero _ (by rintro _ ⟨y, rfl⟩; exact ⟨a y, rfl⟩)).eq_of_tgt _ _
    · exact (hzero _ (by rw [h]; rintro _ ⟨y, rfl⟩; exact ⟨b y, rfl⟩)).eq_of_tgt _ _
    · change a ≫ (hyperplaneFrame n S i).e = b ≫ (hyperplaneFrame n S j).e at h
      have : IsOpenImmersion (hyperplaneFrame n S i).e :=
        inferInstanceAs (IsOpenImmersion (standardOpen (Option n) S (some i)).ι)
      have : HasInvertibleExponent Λ W := .of_hom (a ≫ (hyperplaneFrame n S i).e)
      obtain ⟨g₁, hg₁⟩ : ∃ g, IsPullback g _ _ _ :=
        ⟨_, isPullback_zeroLocusSubschemeι a (Set.range (hyperplaneFrame n S i).f)
          (Set.range fun t ↦ a.appTop ((hyperplaneFrame n S i).f t))
          (by rw [← Set.range_comp]; rfl)⟩
      have hg' := hg₁.paste_horiz (hyperplaneFrame n S i).isPullback
      have hout : IsPullback (g₁ ≫ (hyperplaneFrame n S i).toZ)
          (W.zeroLocusSubschemeι (Set.range fun t ↦ a.appTop ((hyperplaneFrame n S i).f t)))
          (hyperplane n S) (b ≫ (hyperplaneFrame n S j).e) := h ▸ hg'
      let g₂ := (hyperplaneFrame n S j).isPullback.lift (g₁ ≫ (hyperplaneFrame n S i).toZ)
        (W.zeroLocusSubschemeι (Set.range fun t ↦ a.appTop ((hyperplaneFrame n S i).f t)) ≫ b)
        (by rw [hout.w, Category.assoc])
      have hg₂ : IsPullback g₂
          (W.zeroLocusSubschemeι (Set.range fun t ↦ a.appTop ((hyperplaneFrame n S i).f t)))
          _ b :=
        IsPullback.of_right (by rw [IsPullback.lift_fst]; exact hout)
          ((hyperplaneFrame n S j).isPullback.lift_snd _ _ _) (hyperplaneFrame n S j).isPullback
      have := isIso_supportedRestriction_of_isOpenImmersion (ModuleCat.{u + 1} Λ)
        (a ≫ (hyperplaneFrame n S i).e) (hyperplane n S) _ _ hg' _ _
        (leftDerivedUpperStarTateShiftIso Λ _ 1)
      obtain ⟨v, hv⟩ := exists_unit_hyperplaneFrame i j a b h
      let M : Matrix (Fin 1) (Fin 1) Γ(W, ⊤) := Matrix.of fun _ _ ↦ (v : Γ(W, ⊤))
      have hM : IsUnit M.det := by
        rw [Matrix.det_unique]
        exact v.isUnit
      have hMf : (fun t ↦ b.appTop ((hyperplaneFrame n S j).f t)) =
          M.mulVec fun t ↦ a.appTop ((hyperplaneFrame n S i).f t) := by
        funext t
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, M, Matrix.of_apply]
        exact hv
      rw [← cancel_epi (leftDerivedUpperStarConstantComplexIso Λ
          (a ≫ (hyperplaneFrame n S i).e)).inv,
        ← cancel_mono (supportedRestriction (ModuleCat.{u + 1} Λ) (a ≫ (hyperplaneFrame n S i).e)
          (hyperplane n S) _ _ hg' _ _
          (leftDerivedUpperStarTateShiftIso Λ (a ≫ (hyperplaneFrame n S i).e) 1))]
      simp only [Category.assoc]
      exact (constantComplexIso_inv_comp_leftDerivedUpperStarComp_map_supportedRestriction Λ
        (hyperplaneFrame n S i).e a _ rfl (hyperplane n S) _ _ (hyperplaneFrame n S i).toZ
        (hyperplaneFrame n S i).isPullback g₁ hg₁ _ hg' _ _ (hδ i)).trans
        ((restrictSupportedClass_frameClass_eq_of_mulVec Λ (hyperplaneFrame n S i)
          (hyperplaneFrame n S j) (a ≫ (hyperplaneFrame n S i).e ≫ (ℙ(Option n; S) ↘ S) ≫ aS)
          a b M hM (fun t ↦ a.appTop ((hyperplaneFrame n S i).f t))
          (fun t ↦ b.appTop ((hyperplaneFrame n S j).f t)) (fun _ ↦ rfl) (fun _ ↦ rfl) hMf
          g₁ hg₁ g₂ hg₂).trans
        (constantComplexIso_inv_comp_leftDerivedUpperStarComp_map_supportedRestriction Λ
          (hyperplaneFrame n S j).e b _ h (hyperplane n S) _ _ (hyperplaneFrame n S j).toZ
          (hyperplaneFrame n S j).isPullback g₂ hg₂ _ hg' _ _ (hδ j)).symm))
  refine ⟨γ, fun i ↦ ?_⟩
  have h : (L(((hyperplaneFrame n S i).e)^*[ModuleCat.{u + 1} Λ])).map γ = δ (some i) :=
    hγ (some i)
  simp only [frameRestriction, restrictSupportedClass, h]
  simp [δ]

variable (Λ n) in
include aS in
/-- *Uniqueness of the hyperplane class.* Two classes with supports in the hyperplane which agree
on every chart `D₊(Tᵢ)` are equal: they are sections of a sheaf
(`AlgebraicGeometry.Etale.isZero_homology_hyperplaneTarget`), and vanish off the hyperplane. -/
theorem eq_of_frameRestriction_hyperplaneFrame_eq [Finite n]
    {γ γ' : constantComplex Λ ℙ(Option n; S) ⟶ (R(hyperplane n S)_![ModuleCat.{u + 1} Λ]).obj
      ((R(hyperplane n S)^![ModuleCat.{u + 1} Λ]).obj
        ((tateObject Λ ℙ(Option n; S) ((1 : ℕ) : ℤ))⟦2 * ((1 : ℕ) : ℤ)⟧))}
    (h : ∀ i, frameRestriction Λ (hyperplaneFrame n S i) γ =
      frameRestriction Λ (hyperplaneFrame n S i) γ') :
    γ = γ' := by
  let K := (R(hyperplane n S)_![ModuleCat.{u + 1} Λ]).obj
    ((R(hyperplane n S)^![ModuleCat.{u + 1} Λ]).obj
      ((tateObject Λ ℙ(Option n; S) ((1 : ℕ) : ℤ))⟦2 * ((1 : ℕ) : ℤ)⟧))
  have hKz := isZero_homology_hyperplaneTarget (Λ := Λ) (n := n) aS
  have : K.IsGE 0 := (_root_.DerivedCategory.isGE_iff K 0).2 fun m hm ↦ hKz m hm.ne
  have : K.IsLE 0 := (_root_.DerivedCategory.isLE_iff K 0).2 fun m hm ↦ hKz m hm.ne'
  obtain ⟨G, ⟨eM⟩⟩ := _root_.DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE K 0
  refine hom_ext_of_leftDerivedUpperStar_map_eq (constantComplexIsoSingleFunctor Λ _) eM
    fun Ω _ _ x ↦ ?_
  have : Subsingleton (Spec (.of Ω)) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  obtain ⟨y⟩ : Nonempty (Spec (.of Ω)) := inferInstanceAs (Nonempty (PrimeSpectrum Ω))
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((iSup_standardOpen (Option n) S).ge (Set.mem_univ (x.base y)))
  have hxe : Set.range x.base ⊆ Set.range (standardOpen (Option n) S j).ι.base := by
    rintro _ ⟨y', rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim y' y]
    exact hj
  cases j with
  | none =>
    exact (isZero_leftDerivedUpperStar_obj_rightDerivedLowerShriek_of_disjoint _
      (hyperplane n S) (standardOpen (Option n) S none).ι disjoint_range_hyperplane x hxe
      _).eq_of_tgt _ _
  | some i =>
    have : IsOpenImmersion (hyperplaneFrame n S i).e :=
      inferInstanceAs (IsOpenImmersion (standardOpen (Option n) S (some i)).ι)
    have he : (L(((hyperplaneFrame n S i).e)^*[ModuleCat.{u + 1} Λ])).map γ =
        (L(((hyperplaneFrame n S i).e)^*[ModuleCat.{u + 1} Λ])).map γ' := by
      have := isIso_supportedRestriction_of_isOpenImmersion (ModuleCat.{u + 1} Λ)
        (hyperplaneFrame n S i).e (hyperplane n S) _ (hyperplaneFrame n S i).toZ
        (hyperplaneFrame n S i).isPullback _ _
        (leftDerivedUpperStarTateShiftIso Λ (hyperplaneFrame n S i).e 1)
      have h' := h i
      simp only [frameRestriction, restrictSupportedClass] at h'
      rwa [cancel_epi, cancel_mono] at h'
    have hx' := IsOpenImmersion.lift_fac (hyperplaneFrame n S i).e x hxe
    let comp := leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ)
      (IsOpenImmersion.lift (hyperplaneFrame n S i).e x hxe) (hyperplaneFrame n S i).e x hx'.symm
    rw [← NatIso.naturality_2 comp γ, ← NatIso.naturality_2 comp γ', Functor.comp_map,
      Functor.comp_map, he]

variable (Λ n) in
include aS in
/-- The *hyperplane class* `[H] ∈ H²_H(ℙ(Option n; S), Λ(1))`, the unique class with supports in
the hyperplane restricting to `∂κ(T_∗ / Tᵢ)` on every chart `D₊(Tᵢ)`. -/
noncomputable def hyperplaneClass [Finite n] :
    constantComplex Λ ℙ(Option n; S) ⟶ (R(hyperplane n S)_![ModuleCat.{u + 1} Λ]).obj
      ((R(hyperplane n S)^![ModuleCat.{u + 1} Λ]).obj
        ((tateObject Λ ℙ(Option n; S) ((1 : ℕ) : ℤ))⟦2 * ((1 : ℕ) : ℤ)⟧)) :=
  (exists_isHyperplaneClass Λ n aS).choose

include aS in
lemma isHyperplaneClass_hyperplaneClass [Finite n] :
    IsHyperplaneClass Λ n S (hyperplaneClass Λ n aS) :=
  (exists_isHyperplaneClass Λ n aS).choose_spec

include aS in
lemma eq_hyperplaneClass [Finite n]
    {γ : constantComplex Λ ℙ(Option n; S) ⟶ (R(hyperplane n S)_![ModuleCat.{u + 1} Λ]).obj
      ((R(hyperplane n S)^![ModuleCat.{u + 1} Λ]).obj
        ((tateObject Λ ℙ(Option n; S) ((1 : ℕ) : ℤ))⟦2 * ((1 : ℕ) : ℤ)⟧))}
    (hγ : IsHyperplaneClass Λ n S γ) : γ = hyperplaneClass Λ n aS :=
  eq_of_frameRestriction_hyperplaneFrame_eq Λ n aS fun i ↦ by
    rw [hγ i, isHyperplaneClass_hyperplaneClass aS i]

include aS in
/-- *Purity for the hyperplane.* The adjoint `Λ_{ℙ(n; S)} ⟶ RH^! (Λ(1)[2])` of the hyperplane
class is an isomorphism. -/
theorem isIso_supportedClassMap_hyperplaneClass [Finite n] :
    IsIso (supportedClassMap Λ (hyperplane n S) (hyperplaneClass Λ n aS)) := by
  have hΨ : ∀ i, IsIso (supportedRestriction (ModuleCat.{u + 1} Λ) (hyperplaneFrame n S i).e
      (hyperplane n S) _ (hyperplaneFrame n S i).toZ (hyperplaneFrame n S i).isPullback _ _
      (leftDerivedUpperStarTateShiftIso Λ (hyperplaneFrame n S i).e ((1 : ℕ) : ℤ))) := fun i ↦ by
    have : IsOpenImmersion (hyperplaneFrame n S i).e :=
      inferInstanceAs (IsOpenImmersion (standardOpen (Option n) S (some i)).ι)
    exact isIso_supportedRestriction_of_isOpenImmersion _ _ _ _ _ _ _ _ _
  refine isIso_of_isIso_leftDerivedUpperStar_map_of_jointlySurjective Λ
    (fun i ↦ (hyperplaneFrame n S i).toZ) (fun s ↦ ?_) _ fun i ↦ ?_
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_standardOpen n S).ge (Set.mem_univ s))
    obtain ⟨w, hw⟩ : hyperplane n S s ∈
        Set.range (standardOpen (Option n) S (some i)).ι.base := by
      rw [Scheme.Opens.range_ι]
      change s ∈ hyperplane n S ⁻¹ᵁ standardOpen (Option n) S (some i)
      rw [hyperplane_preimage_standardOpen_some]
      exact hi
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := hyperplane n S) (g := (hyperplaneFrame n S i).e) s w hw.symm
    refine ⟨i, (hyperplaneFrame n S i).isPullback.isoPullback.inv z, ?_⟩
    rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst]
    exact hz
  · refine (isIso_supportedClassMap_restrictSupportedClass_iff Λ (hyperplaneFrame n S i).e
      (hyperplane n S) _ (hyperplaneFrame n S i).toZ (hyperplaneFrame n S i).isPullback _ _
      (leftDerivedUpperStarTateShiftIso Λ (hyperplaneFrame n S i).e ((1 : ℕ) : ℤ))
      (hyperplaneClass Λ n aS) (hΨ i)).1 ?_
    have h := isHyperplaneClass_hyperplaneClass (Λ := Λ) aS i
    rw [frameRestriction] at h
    rw [h]
    exact isIso_supportedClassMap_hyperplaneFrame aS i

variable (Λ S) in
/-- The projective-space formula for `ℙ(Option n; S)` and every hyperplane class. -/
def ProjectiveFormula (n : Type u) [Fintype n] : Prop :=
  ∀ γ : constantComplex Λ ℙ(Option n; S) ⟶ (R(hyperplane n S)_![ModuleCat.{u + 1} Λ]).obj
      ((R(hyperplane n S)^![ModuleCat.{u + 1} Λ]).obj
        ((tateObject Λ ℙ(Option n; S) ((1 : ℕ) : ℤ))⟦2 * ((1 : ℕ) : ℤ)⟧)),
    IsHyperplaneClass Λ n S γ →
      IsIso (projectiveFormulaMap (ℙ(Option n; S) ↘ S) (hyperplaneChernClass γ) (Fintype.card n))

omit [HasKummerClass.IsNormalized Λ] in
/-- *Induction step 0 of the projective-space formula*: `ℙ⁰_S = S`, and `Λ_S ⟶ Rq_* Λ` is an
isomorphism.

`ℙ(Option PEmpty; S) ⟶ S` is an isomorphism, so the unit is one, and the map is
the unit up to the identification `Λ_S(0)[0] ≅ Λ_S`. -/
lemma projectiveFormula_pempty : ProjectiveFormula Λ S PEmpty := by
  intro γ _
  have : Unique (Option PEmpty.{u + 1}) := ⟨⟨none⟩, fun a ↦ by cases a with
    | none => rfl
    | some x => exact x.elim⟩
  exact isIso_projectiveFormulaMap_of_eq_zero _ _ _ Fintype.card_eq_zero

include aS in
/-- *Invariance under renaming the coordinates* of the projective-space formula.

Not proved here: an equivalence `n ≃ n'` induces an isomorphism `ℙ(Option n; S) ≅ ℙ(Option n'; S)`
over `S` carrying the hyperplane to the hyperplane, hence hyperplane classes to hyperplane
classes (`AlgebraicGeometry.Etale.eq_hyperplaneClass`). -/
lemma projectiveFormula_of_equiv {n n' : Type u} [Fintype n] [Fintype n'] (e : n ≃ n')
    (h : ProjectiveFormula Λ S n) : ProjectiveFormula Λ S n' := by
  sorry

include aS in
/-- *Induction step of the projective-space formula*, by the localization triangle of
`𝔸 ⊂ ℙ(Option (Option n); S) ⊃ ℙ(Option n; S)`.

Not proved here. Apply `Rq_*` to `j_! j^* Λ ⟶ Λ ⟶ H_* H^* Λ`, with `j` the open immersion of
`D₊(T_∗) ≅ 𝔸^{r+1}_S` and `H` the hyperplane. The first term is `Rp_! Λ ≅ Λ_S(-r-1)[-2r-2]`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_twistShift_affineSpace`). The last
is `⊕_{a ≤ r} Λ_S(-a)[-2a]` by the induction hypothesis, compatibly with `hᵃ` since `h` restricts
to `h` (`AlgebraicGeometry.Etale.classRestriction_hyperplane_hyperplaneChernClass_eq`). The top
power `h^{r+1}` restricts to zero on the hyperplane and corresponds to the generator of the first
term. -/
lemma projectiveFormula_option {n : Type u} [Fintype n] (h : ProjectiveFormula Λ S n) :
    ProjectiveFormula Λ S (Option n) := by
  sorry

include aS in
/-- Blueprint `thm-pur-projective-bundle-formula`: Projective-bundle formula without purity

*The trivial bundle.* For the projective space `q : ℙⁿ_S = ℙ(Option n; S) ⟶ S`, `n` with `r`
elements, over a separated scheme of finite type over a field on which the exponent of `Λ` is
invertible, and `h = c₁(𝒪(1))` the first Chern class of a hyperplane class
(`AlgebraicGeometry.Etale.hyperplaneChernClass`),

`(1, h, …, hʳ) : ⊕_{a ≤ r} Λ_S(-a)[-2a] ⟶ Rq_* Λ_{ℙʳ_S}`

is an isomorphism. The blueprint states the formula for the projectivization `ℙ_B(F)` of any
vector bundle `F`; the projectivization of a vector bundle is not constructed in this repository,
and the formula for it follows from this case by restriction to trivialising opens.

By induction on `n` (`Fintype.induction_empty_option`) from `projectiveFormula_pempty`,
`projectiveFormula_of_equiv` and the localization step `projectiveFormula_option`, which are
stated and not proved. -/
theorem isIso_projectiveFormulaMap [Fintype n]
    (γ : constantComplex Λ ℙ(Option n; S) ⟶ (R(hyperplane n S)_![ModuleCat.{u + 1} Λ]).obj
      ((R(hyperplane n S)^![ModuleCat.{u + 1} Λ]).obj
        ((tateObject Λ ℙ(Option n; S) ((1 : ℕ) : ℤ))⟦2 * ((1 : ℕ) : ℤ)⟧)))
    (hγ : IsHyperplaneClass Λ n S γ) :
    IsIso (projectiveFormulaMap (ℙ(Option n; S) ↘ S) (hyperplaneChernClass γ)
      (Fintype.card n)) := by
  have key : ∀ (n : Type u) [Fintype n], ProjectiveFormula Λ S n :=
    Fintype.induction_empty_option (P := fun n _ ↦ ProjectiveFormula Λ S n)
      (fun _ β _ e h ↦ letI := Fintype.ofEquiv β e.symm; projectiveFormula_of_equiv aS e h)
      projectiveFormula_pempty
      (fun _ _ h ↦ projectiveFormula_option aS h)
  exact key n γ hγ

attribute [local instance] HasInvertibleExponent.opens

/-- The restriction of a class `h ∈ H^{2m}(Y, Λ(m))` along `g : X ⟶ Y`. -/
noncomputable def restrictClass {X Y : Scheme.{u}} [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ Y] (g : X ⟶ Y) {m : ℤ}
    (h : constantComplex Λ Y ⟶ (tateObject Λ Y m)⟦2 * m⟧) :
    constantComplex Λ X ⟶ (tateObject Λ X m)⟦2 * m⟧ :=
  (leftDerivedUpperStarConstantComplexIso Λ g).inv ≫ (L((g)^*[ModuleCat.{u + 1} Λ])).map h ≫
    (leftDerivedUpperStarTateShiftIso Λ g m).hom

/-- A *projective bundle* of relative dimension given by `n`: a morphism `p : P ⟶ B` together
with an open cover `(U i)` of `B` and isomorphisms `p⁻¹(U i) ≅ ℙ(Option n; U i)` over `U i`. The
projectivization `ℙ_B(F)` of a vector bundle `F` of rank `#n + 1` is one. -/
structure ProjectiveBundle {P B : Scheme.{u}} (n : Type u) (p : P ⟶ B) where
  /-- The index type of the trivialising cover. -/
  ι : Type u
  /-- The trivialising opens of the base. -/
  U : ι → B.Opens
  iSup_U : iSup U = ⊤
  /-- The trivialisations. -/
  chart (i : ι) : (p ⁻¹ᵁ U i).toScheme ≅ ℙ(Option n; U i)
  chart_over (i : ι) : (chart i).hom ≫ ℙ(Option n; U i) ↘ U i = p ∣_ U i

include aS in
/-- Blueprint `thm-pur-projective-bundle-formula`: Projective-bundle formula without purity

Let `p : P ⟶ B` be a projective bundle of relative dimension `r = #n`
(`AlgebraicGeometry.Etale.ProjectiveBundle`), for instance the projectivization `ℙ_B(F)` of a
vector bundle `F` of rank `r + 1`, over a separated scheme of finite type over a field on which the
exponent of `Λ` is invertible, and let `h ∈ H²(P, Λ(1))` be a class restricting on every chart
`p⁻¹(U i) ≅ ℙʳ_{U i}` to the first Chern class of `𝒪(1)`, the hyperplane class (for `ℙ_B(F)`,
`h = c₁(𝒪(1))`). Then

`(1, h, …, hʳ) : ⊕_{a ≤ r} Λ_B(-a)[-2a] ⟶ Rp_* Λ_P`

is an isomorphism.

Not proved here: on the charts this is
`AlgebraicGeometry.Etale.isIso_projectiveFormulaMap`, and the formation of `Rp_*` commutes with
restriction to the opens of the base. -/
theorem isIso_projectiveFormulaMap_of_projectiveBundle [Fintype n] {P B : Scheme.{u}}
    [HasInvertibleExponent Λ P] [HasInvertibleExponent Λ B] (aB : B ⟶ Spec (.of k))
    [IsSeparated aB] [LocallyOfFiniteType aB] {p : P ⟶ B} (E : ProjectiveBundle n p)
    (h : constantComplex Λ P ⟶ (tateObject Λ P 1)⟦2 * (1 : ℤ)⟧)
    (hh : ∀ i, ∃ γ, IsHyperplaneClass Λ n (E.U i) γ ∧
      restrictClass ((E.chart i).inv ≫ (p ⁻¹ᵁ E.U i).ι) h = hyperplaneChernClass γ) :
    IsIso (projectiveFormulaMap p h (Fintype.card n)) := by
  sorry

section TwistBundle

/-! ### The hyperplane class and the Thom class of `𝒪(1)` -/

variable (n S) in
lemma isPullback_twistBundleZero :
    IsPullback (𝟙 ℙ(n; S)) (twistBundleZero n S) (hyperplane n S) (twistBundleOpen n S).ι :=
  (IsOpenImmersion.isPullback_lift_id _ _ _).flip

variable (Λ n) in
include aS in
/-- The hyperplane class restricted to the total space `W ⊆ ℙ(Option n; S)` of `𝒪(1)`, a class
with supports in the zero section. -/
noncomputable def twistBundleHyperplaneClass [Finite n] :
    constantComplex Λ (twistBundleOpen n S).toScheme ⟶
      (R((twistBundle n S).zero)_![ModuleCat.{u + 1} Λ]).obj
        ((R((twistBundle n S).zero)^![ModuleCat.{u + 1} Λ]).obj
          ((tateObject Λ (twistBundleOpen n S).toScheme ((1 : ℕ) : ℤ))⟦2 * ((1 : ℕ) : ℤ)⟧)) :=
  restrictSupportedClass (ModuleCat.{u + 1} Λ) (twistBundleOpen n S).ι (hyperplane n S)
    (twistBundle n S).zero (𝟙 _) (isPullback_twistBundleZero n S)
    (leftDerivedUpperStarConstantComplexIso Λ _).inv
    (leftDerivedUpperStarTateShiftIso Λ _ ((1 : ℕ) : ℤ)) (hyperplaneClass Λ n aS)

variable (n S) in
/-- The chart `π⁻¹(D₊(Tᵢ)) ⟶ D₊(T_{some i})` of the total space of `𝒪(1)` in `ℙ(Option n; S)`. -/
noncomputable def twistBundleToStandardOpen (i : n) :
    (twistBundleπ n S ⁻¹ᵁ standardOpen n S i).toScheme ⟶
      (standardOpen (Option n) S (some i)).toScheme :=
  IsOpenImmersion.lift (standardOpen (Option n) S (some i)).ι
    ((twistBundleπ n S ⁻¹ᵁ standardOpen n S i).ι ≫ (twistBundleOpen n S).ι) (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      have hx : x.1 ∈ (twistBundleOpen n S).ι ⁻¹ᵁ standardOpen (Option n) S (some i) := by
        rw [← twistBundleπ_preimage_standardOpen]
        exact x.2
      exact hx)

variable (n S) in
@[reassoc (attr := simp)]
lemma twistBundleToStandardOpen_ι (i : n) :
    twistBundleToStandardOpen n S i ≫ (standardOpen (Option n) S (some i)).ι =
      (twistBundleπ n S ⁻¹ᵁ standardOpen n S i).ι ≫ (twistBundleOpen n S).ι :=
  IsOpenImmersion.lift_fac _ _ _

variable (n S) in
/-- The local equation `T_∗ / Tᵢ` of the hyperplane pulls back to the fibre coordinate of `𝒪(1)`. -/
lemma twistBundleToStandardOpen_appTop_frame (i : n) (a : Fin 1) :
    (twistBundleToStandardOpen n S i).appTop ((hyperplaneFrame n S i).f a) =
      (twistBundle n S).coord i a := by
  rw [twistBundle_coord]
  change (twistBundleToStandardOpen n S i).appTop
    ((standardOpenIso (Option n) S (some i)).hom.appTop (AffineSpace.coord S ⟨none, by simp⟩)) = _
  rw [standardOpenIso_hom_appTop_coord, twistBundleFiberCoord]
  have e₀ : (standardOpen (Option n) S (some i)).topIso.inv =
      (standardOpen (Option n) S (some i)).ι.appLE (standardOpen (Option n) S (some i)) ⊤
        (Scheme.Opens.ι_preimage_self _).ge := by
    rw [Scheme.Opens.ι_appLE]
    rfl
  have e₁ : (twistBundleπ n S ⁻¹ᵁ standardOpen n S i).topIso.inv =
      (twistBundleπ n S ⁻¹ᵁ standardOpen n S i).ι.appLE (twistBundleπ n S ⁻¹ᵁ standardOpen n S i)
        ⊤ (Scheme.Opens.ι_preimage_self _).ge := by
    rw [Scheme.Opens.ι_appLE]
    rfl
  have e₂ : (twistBundleToStandardOpen n S i).appTop =
      (twistBundleToStandardOpen n S i).appLE ⊤ ⊤ le_top := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  rw [e₀, e₁, e₂, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
    Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE,
    appLE_eq_of_eq (twistBundleToStandardOpen_ι n S i)]

include aS in
/-- On every chart of `𝒪(1)` the restricted hyperplane class is the Kummer class of the fibre
coordinate `T_∗ / Tᵢ`, the frame class of the chart. -/
lemma frameRestriction_twistBundleHyperplaneClass [Finite n] (i : n) :
    frameRestriction Λ ((twistBundle n S).frame i) (twistBundleHyperplaneClass Λ n aS) =
      frameClass Λ ((twistBundle n S).frame i) := by
  have hb : ((twistBundle n S).frame i).e ≫ (twistBundleOpen n S).ι =
      twistBundleToStandardOpen n S i ≫ (hyperplaneFrame n S i).e :=
    (twistBundleToStandardOpen_ι n S i).symm
  obtain ⟨g₁, hg₁⟩ : ∃ g, IsPullback g
      (((twistBundle n S).frame i).U.zeroLocusSubschemeι (Set.range ((twistBundle n S).frame i).f))
      ((hyperplaneFrame n S i).U.zeroLocusSubschemeι (Set.range (hyperplaneFrame n S i).f))
      (twistBundleToStandardOpen n S i) :=
    ⟨_, isPullback_zeroLocusSubschemeι (twistBundleToStandardOpen n S i)
      (Set.range (hyperplaneFrame n S i).f) (Set.range ((twistBundle n S).frame i).f) (by
        rw [← Set.range_comp]
        exact congrArg Set.range (funext fun a ↦ twistBundleToStandardOpen_appTop_frame n S i a))⟩
  have hp₁ := ((twistBundle n S).frame i).isPullback.paste_horiz (isPullback_twistBundleZero n S)
  have : HasInvertibleExponent Λ ((twistBundle n S).frame i).U :=
    .of_hom ((twistBundle n S).frame i).e
  have : HasInvertibleExponent Λ (hyperplaneFrame n S i).U := .of_hom (hyperplaneFrame n S i).e
  rw [frameRestriction, twistBundleHyperplaneClass, ← restrictSupportedClass_comp_tateShift Λ
    ((twistBundle n S).frame i).e (twistBundleOpen n S).ι _ rfl (hyperplane n S)
    (twistBundle n S).zero _ (𝟙 _) (isPullback_twistBundleZero n S)
    ((twistBundle n S).frame i).toZ ((twistBundle n S).frame i).isPullback _ hp₁,
    restrictSupportedClass_comp_tateShift Λ (twistBundleToStandardOpen n S i)
    (hyperplaneFrame n S i).e _ hb (hyperplane n S) _ _ (hyperplaneFrame n S i).toZ
    (hyperplaneFrame n S i).isPullback g₁ hg₁ _ hp₁]
  have hH := isHyperplaneClass_hyperplaneClass (Λ := Λ) aS i
  rw [frameRestriction] at hH
  rw [hH, frameClass, frameClass]
  exact restrictSupportedClass_kummerBoundaryProduct Λ (twistBundleToStandardOpen n S i) _ _
    (twistBundleToStandardOpen_appTop_frame n S i) g₁ hg₁

include aS in
/-- **The hyperplane class restricts to the Thom class of `𝒪(1)`** on the total space
`W ⊆ ℙ(Option n; S)`: both are classes with supports in the zero section `ℙ(n; S) = H` restricting
to the Kummer class of `T_∗ / Tᵢ` on every chart
(`AlgebraicGeometry.Etale.frameRestriction_twistBundleHyperplaneClass`). -/
theorem twistBundleHyperplaneClass_eq_thomClass [Finite n] :
    twistBundleHyperplaneClass Λ n aS = (twistBundle n S).thomClass Λ (ℙ(n; S) ↘ S ≫ aS) :=
  haveI : Finite (twistBundle n S).ι := inferInstanceAs (Finite n)
  (twistBundle n S).eq_thomClass_of_frameRestriction Λ _
    (frameRestriction_twistBundleHyperplaneClass aS)

include aS in
/-- **The hyperplane class restricted to the hyperplane is `c₁(𝒪(1))`**: the restriction of
`h = c₁(𝒪(1)) ∈ H²(ℙ(Option n; S), Λ(1))` along the hyperplane embedding `ℙ(n; S) ⟶ ℙ(Option n; S)`
is the top Chern class of the line bundle `𝒪(1)` on `ℙ(n; S)`: the hyperplane class restricts on
the total space of `𝒪(1)` to its Thom class (`twistBundleHyperplaneClass_eq_thomClass`), and
the zero section of `𝒪(1)` is the hyperplane embedding. -/
theorem classRestriction_hyperplane_hyperplaneChernClass [Finite n] :
    VectorBundle.classRestriction Λ (r := 1) (hyperplane n S)
        (hyperplaneChernClass (hyperplaneClass Λ n aS)) =
      (twistBundle n S).topChernClass Λ (ℙ(n; S) ↘ S ≫ aS) := by
  rw [VectorBundle.topChernClass, VectorBundle.localizedTopChernForget_eq,
    ← twistBundleHyperplaneClass_eq_thomClass,
    VectorBundle.classRestriction_comp Λ (twistBundleZero n S) (twistBundleOpen n S).ι
      (hyperplane n S) (twistBundleZero_ι n S).symm]
  congr 1
  simp only [VectorBundle.classRestriction, hyperplaneChernClass, twistBundleHyperplaneClass,
    restrictSupportedClass, Functor.map_comp, Category.assoc, supportedRestriction_comp_counit]

include aS in
/-- **`c₁(𝒪(1))` is the hyperplane class.** On `ℙ(Option m; S)`, the top Chern class of the line
bundle `𝒪(1)` is the first Chern class `h` of the hyperplane class of `V(T_∗)`.

Not proved here. Let `σ = twistBundleSection (Option m) S none : ℙ(Option m; S) ⟶ W` be the
section `[x] ↦ [x : x_∗]` of `𝒪(1)` (`twistBundleSection_comp_π`). By (L4) and
`localizedTopChernForget_eq`, `c₁(𝒪(1)) = σ^* (forget th)`, and by
`twistBundleHyperplaneClass_eq_thomClass` and `classRestriction_comp` this is the restriction of
`h_{ℙ(Option (Option m))}` along `σ ≫ W.ι`. It remains to see that this restriction is `h`: the
square `(hyperplane m, σ ≫ W.ι, hyperplane (Option m))` is cartesian (`x_∗ = 0`), so the
restriction is `forget` of the restriction of supports of the hyperplane class
(`supportedRestriction_comp_counit`), which restricts on the chart `D₊(Tᵢ)` to the Kummer class
of the pull-back `x_∗ / xᵢ` of `T_∗∗ / Tᵢ` (`restrictSupportedClass_kummerBoundaryProduct`,
`restrictSupportedClass_comp_tateShift`), hence is the hyperplane class by
`eq_of_frameRestriction_hyperplaneFrame_eq`. -/
theorem topChernClass_twistBundle_eq_hyperplaneChernClass {m : Type u} [Finite m] :
    (twistBundle (Option m) S).topChernClass Λ (ℙ(Option m; S) ↘ S ≫ aS) =
      hyperplaneChernClass (hyperplaneClass Λ m aS) := by
  have hsq := (isPullback_hyperplane_twistBundleSectionAux S (m := m)).flip
  let δ := restrictSupportedClass (ModuleCat.{u + 1} Λ) (twistBundleSectionAux (Option m) S none)
    (hyperplane (Option m) S) (hyperplane m S) (hyperplane m S) hsq
    (leftDerivedUpperStarConstantComplexIso Λ _).inv
    (leftDerivedUpperStarTateShiftIso Λ _ ((1 : ℕ) : ℤ)) (hyperplaneClass Λ (Option m) aS)
  have hframe : ∀ k : m, frameRestriction Λ (hyperplaneFrame m S k) δ =
      frameClass Λ (hyperplaneFrame m S k) := by
    intro k
    have hb₀ : Set.range ((standardOpen (Option m) S (some k)).ι ≫
        twistBundleSectionAux (Option m) S none).base ⊆
        Set.range (standardOpen (Option (Option m)) S (some (some k))).ι.base := by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      have hx : x.1 ∈ twistBundleSectionAux (Option m) S none ⁻¹ᵁ
          standardOpen (Option (Option m)) S (some (some k)) := by
        rw [twistBundleSectionAux_preimage_standardOpen_some]
        exact x.2
      exact hx
    let b := IsOpenImmersion.lift _ _ hb₀
    have hbι : b ≫ (standardOpen (Option (Option m)) S (some (some k))).ι =
        (standardOpen (Option m) S (some k)).ι ≫ twistBundleSectionAux (Option m) S none :=
      IsOpenImmersion.lift_fac _ _ _
    have hv : b.appTop ((standardOpenIso (Option (Option m)) S (some (some k))).hom.appTop
        (extraCoord (Option m) S (some k))) =
        (standardOpenIso (Option m) S (some k)).hom.appTop (extraCoord m S k) := by
      change b.appTop ((standardOpenIso _ S _).hom.appTop (AffineSpace.coord S ⟨none, by simp⟩)) =
        (standardOpenIso _ S _).hom.appTop (AffineSpace.coord S ⟨none, by simp⟩)
      rw [standardOpenIso_hom_appTop_coord, standardOpenIso_hom_appTop_coord]
      have e₀ : (standardOpen (Option (Option m)) S (some (some k))).topIso.inv =
          (standardOpen (Option (Option m)) S (some (some k))).ι.appLE
            (standardOpen (Option (Option m)) S (some (some k))) ⊤
            (Scheme.Opens.ι_preimage_self _).ge := by
        rw [Scheme.Opens.ι_appLE]
        rfl
      have e₂ : b.appTop = b.appLE ⊤ ⊤ le_top := by
        rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
        rfl
      have hh : (standardOpen (Option m) S (some k)).ι ≫ twistBundleSectionAux (Option m) S none =
          homOfSections ((standardOpen (Option m) S (some k)).ι ≫ ℙ(Option m; S) ↘ S)
            (fun a ↦ (standardOpen (Option m) S (some k)).topIso.inv
              ((twistBundleSectionSections (Option m) S none a).s (some k)))
            (Scheme.CoordinateCover.span_topIso_inv _
              (span_twistBundleSectionSections (Option m) S none) (some k)) :=
        Scheme.CoordinateCover.ι_hom (𝒟 := standardCoordinateCover (Option m) S) _ _ _ _
      rw [e₀, e₂, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, appLE_eq_of_eq hbι,
        appLE_eq_of_eq hh]
      exact (homOfSections_appLE_coordRatio (S := S) _
        (fun a ↦ (standardOpen (Option m) S (some k)).topIso.inv
          ((twistBundleSectionSections (Option m) S none a).s (some k)))
        (Scheme.CoordinateCover.span_topIso_inv _
          (span_twistBundleSectionSections (Option m) S none) (some k))
        (twistBundleSectionSections_some_s_self (Option m) S none (some k)) none _).trans rfl
    have hz := isPullback_zeroLocusSubschemeι b
      (Set.range fun _ : Fin 1 ↦ (standardOpenIso (Option (Option m)) S (some (some k))).hom.appTop
        (extraCoord (Option m) S (some k)))
      (Set.range fun _ : Fin 1 ↦ (standardOpenIso (Option m) S (some k)).hom.appTop
        (extraCoord m S k))
      (by rw [← Set.range_comp]; exact congrArg Set.range (funext fun _ ↦ hv))
    have : HasInvertibleExponent Λ (hyperplaneFrame m S k).U := .of_hom (hyperplaneFrame m S k).e
    have : HasInvertibleExponent Λ (hyperplaneFrame (Option m) S (some k)).U :=
      .of_hom (hyperplaneFrame (Option m) S (some k)).e
    have hp := (hyperplaneFrame m S k).isPullback.paste_horiz hsq
    rw [frameRestriction, ← restrictSupportedClass_comp_tateShift Λ (hyperplaneFrame m S k).e
      (twistBundleSectionAux (Option m) S none) _ rfl (hyperplane (Option m) S) (hyperplane m S) _
      (hyperplane m S) hsq (hyperplaneFrame m S k).toZ (hyperplaneFrame m S k).isPullback _ hp]
    refine (restrictSupportedClass_comp_tateShift Λ b (hyperplaneFrame (Option m) S (some k)).e
      ((hyperplaneFrame m S k).e ≫ twistBundleSectionAux (Option m) S none)
      hbι.symm (hyperplane (Option m) S) _ _ (hyperplaneFrame (Option m) S (some k)).toZ
      (hyperplaneFrame (Option m) S (some k)).isPullback _ hz _ hp).trans ?_
    have hH := isHyperplaneClass_hyperplaneClass (Λ := Λ) aS (some k)
    rw [frameRestriction] at hH
    rw [hH, frameClass, frameClass]
    exact restrictSupportedClass_kummerBoundaryProduct Λ b _ _ (fun _ ↦ hv) _ hz
  have hδ : δ = hyperplaneClass Λ m aS := eq_hyperplaneClass aS hframe
  sorry

include aS in
/-- **The hyperplane class restricts to the hyperplane class**: along the hyperplane embedding
`ℙ(Option m; S) ⟶ ℙ(Option (Option m); S)`, `h` restricts to `h`. This is the compatibility used
in the localization induction for the projective-space formula. -/
theorem classRestriction_hyperplane_hyperplaneChernClass_eq {m : Type u} [Finite m] :
    VectorBundle.classRestriction Λ (r := 1) (hyperplane (Option m) S)
        (hyperplaneChernClass (hyperplaneClass Λ (Option m) aS)) =
      hyperplaneChernClass (hyperplaneClass Λ m aS) := by
  rw [classRestriction_hyperplane_hyperplaneChernClass,
    topChernClass_twistBundle_eq_hyperplaneChernClass]

end TwistBundle

end Etale

end AlgebraicGeometry
