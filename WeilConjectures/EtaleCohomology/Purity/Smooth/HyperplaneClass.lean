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

Not proved here: the blueprint proof computes `RΓ(ℙʳ_k, Λ)` over an algebraically closed field by
the localization triangle of `𝔸ʳ ⊂ ℙʳ ⊃ ℙ^{r-1}` and induction, then concludes by proper base
change. -/
theorem isIso_projectiveFormulaMap [Fintype n]
    (γ : constantComplex Λ ℙ(Option n; S) ⟶ (R(hyperplane n S)_![ModuleCat.{u + 1} Λ]).obj
      ((R(hyperplane n S)^![ModuleCat.{u + 1} Λ]).obj
        ((tateObject Λ ℙ(Option n; S) ((1 : ℕ) : ℤ))⟦2 * ((1 : ℕ) : ℤ)⟧)))
    (hγ : IsHyperplaneClass Λ n S γ) :
    IsIso (projectiveFormulaMap (ℙ(Option n; S) ↘ S) (hyperplaneChernClass γ)
      (Fintype.card n)) := by
  sorry
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

end TwistBundle

end Etale

end AlgebraicGeometry
