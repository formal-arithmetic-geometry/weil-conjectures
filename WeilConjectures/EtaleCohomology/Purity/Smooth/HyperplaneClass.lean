/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Hyperplane
public import WeilConjectures.EtaleCohomology.Purity.Smooth.ProjectiveLineChern
public import WeilConjectures.EtaleCohomology.Purity.Smooth.RegularImmersion

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
        Iso.inv_hom_id_assoc]⟩
  have P₃ := (isPullback_morphismRestrict (hyperplane n S)
    (standardOpen (Option n) S (some i))).flip
  have h := (P₁.paste_horiz P₂).paste_horiz P₃
  rw [Iso.hom_inv_id_assoc] at h
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

end Etale

end AlgebraicGeometry
