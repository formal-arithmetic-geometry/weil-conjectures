/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Hyperplane
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

is an isomorphism (`AlgebraicGeometry.Etale.isIso_projectiveSpaceFormulaMap`, the case of a
trivial bundle of `thm-pur-projective-bundle-formula`).
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

variable (Λ n) in
include aS in
/-- Blueprint `lem-pur-divisor-class`: Divisor classes

*Existence of the hyperplane class.* The Kummer classes `∂κ(T_∗ / Tᵢ)` of the local equations of
the coordinate hyperplane glue to a class with supports in the hyperplane.

Not proved here: the gluing is that of `AlgebraicGeometry.VectorBundle.exists_thomClass`, the
frames on `D₊(Tᵢ) ∩ D₊(Tⱼ)` differing by the unit `Tᵢ / Tⱼ`. -/
theorem exists_isHyperplaneClass :
    ∃ γ, IsHyperplaneClass Λ n S γ := by
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

end Etale

end AlgebraicGeometry
