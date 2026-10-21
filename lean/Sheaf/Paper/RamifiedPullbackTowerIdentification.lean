/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.Paper.RamifiedPullbackTowerData
import Sheaf.Paper.RamifiedCoefficientQuotientComparison
import Sheaf.Paper.RamifiedFinitePullbackComparison
import Sheaf.Paper.FinitePullbackTransitionGenerators
import all Sheaf.Paper.CompletedIntegralProjectionDivisibility

/-! # Ramified identification of finite pullback towers

The arithmetic construction and factorization of the normalized finite comparison.
Source: Stacks 093M, 03EK, 03EL; Bhatt--Scholze 6.8.2(1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings
namespace WeilConjectures.RamifiedPullback
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)

private theorem ramification_exists :
    ∃ e : ℕ, 1 ≤ e ∧
      Ideal.span ({integralScalarIntegerInclusion l E L ι
        (Padic.coefficientExtensionUniformizer l E)} :
          Set (Padic.coefficientExtensionIntegers l L)) =
        Ideal.span {Padic.coefficientExtensionUniformizer l L ^ e} ∧
      ∀ k : ℕ, 1 ≤ k →
        Ideal.span ({integralScalarIntegerInclusion l E L ι
          (Padic.coefficientExtensionUniformizer l E)} :
            Set (Padic.coefficientExtensionIntegers l L)) =
          Ideal.span {Padic.coefficientExtensionUniformizer l L ^ k} → k = e := by
  let R := Padic.coefficientExtensionIntegers l E
  let S := Padic.coefficientExtensionIntegers l L
  let t := Padic.coefficientExtensionUniformizer l E
  let v := Padic.coefficientExtensionUniformizer l L
  let f := integralScalarIntegerInclusion l E L ι
  have hE := (Padic.extension_integers_dvr l E (Padic.coefficientExtensionAbsoluteValue l E)
    (spectralNorm_extends (K := ℚ_[l]) (L := E))).choose_spec.choose_spec
  have hL := (Padic.extension_integers_dvr l L (Padic.coefficientExtensionAbsoluteValue l L)
    (spectralNorm_extends (K := ℚ_[l]) (L := L))).choose_spec.choose_spec
  have : IsLocalRing R := hE.2.2.2.1
  have : IsLocalRing S := hL.2.2.2.1
  have : IsDiscreteValuationRing R := hE.2.2.2.2.2.2.2.1
  have : IsDiscreteValuationRing S := hL.2.2.2.2.2.2.2.1
  have ht : Ideal.span ({t} : Set R) = Padic.coefficientExtensionMaximalIdeal l E :=
    hE.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hv : Ideal.span ({v} : Set S) = Padic.coefficientExtensionMaximalIdeal l L :=
    hL.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hti : Irreducible t :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mpr
      ((hE.2.2.2.2.2.1 _ (IsLocalRing.maximalIdeal.isMaximal R)).trans ht.symm)
  have hvi : Irreducible v :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer v).mpr
      ((hL.2.2.2.2.2.1 _ (IsLocalRing.maximalIdeal.isMaximal S)).trans hv.symm)
  have hft : f t ≠ 0 := by
    intro hz
    have hz' : ι (t : E) = 0 := congrArg Subtype.val hz
    exact hti.ne_zero (Subtype.ext (ι.injective (by simpa using hz')))
  have hnu : ¬ IsUnit (f t) := by
    intro h
    have ha := (hL.2.2.1 (f t)).mp h
    change Padic.coefficientExtensionAbsoluteValue l L (ι (t : E)) = 1 at ha
    rw [integralScalar_absoluteValue l E L ι] at ha
    have hb := (hE.2.1 t).mp
      (show t ∈ Padic.coefficientExtensionMaximalIdeal l E from
        ht ▸ Ideal.mem_span_singleton_self t)
    exact (ne_of_lt hb) ha
  obtain ⟨e, w, heq⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hft hvi
  have he : 1 ≤ e := by
    by_contra hn
    have hz : e = 0 := by omega
    apply hnu
    rw [hz, pow_zero, mul_one] at heq
    exact heq.symm ▸ w.isUnit
  have hideal : Ideal.span ({f t} : Set S) = Ideal.span {v ^ e} := by
    rw [heq]
    exact Ideal.span_singleton_mul_left_unit w.isUnit _
  refine ⟨e, he, hideal, ?_⟩
  intro k _ hk
  have ha := Ideal.span_singleton_eq_span_singleton.mp (hk.symm.trans hideal)
  exact Nat.le_antisymm
    ((pow_dvd_pow_iff hvi.ne_zero hvi.not_isUnit).mp ha.dvd)
    ((pow_dvd_pow_iff hvi.ne_zero hvi.not_isUnit).mp ha.symm.dvd)

private theorem ramified_kernel (e n : ℕ)
    (he : Ideal.span ({integralScalarIntegerInclusion l E L ι
      (Padic.coefficientExtensionUniformizer l E)} :
        Set (Padic.coefficientExtensionIntegers l L)) =
      Ideal.span {Padic.coefficientExtensionUniformizer l L ^ e})
    (hexp : index e n + 1 = e * (n + 1))
    (x : Padic.coefficientExtensionIntegers l E)
    (hx : x ∈ Padic.coefficientExtensionIdeal l E (n + 1)) :
    Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (index e n + 1))
      (integralScalarIntegerInclusion l E L ι x) = 0 := by
  let f := integralScalarIntegerInclusion l E L ι
  have hi : Ideal.map f (Padic.coefficientExtensionIdeal l E (n + 1)) =
      Padic.coefficientExtensionIdeal l L (index e n + 1) := by
    simp only [Padic.coefficientExtensionIdeal, Ideal.map_pow]
    rw [Ideal.map_span, Set.image_singleton, he, ← Ideal.span_singleton_pow,
      ← pow_mul, hexp]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [← hi]
  exact Ideal.mem_map_of_mem f hx

private def ramifiedQuotient (e n : ℕ)
    (he : Ideal.span ({integralScalarIntegerInclusion l E L ι
      (Padic.coefficientExtensionUniformizer l E)} :
        Set (Padic.coefficientExtensionIntegers l L)) =
      Ideal.span {Padic.coefficientExtensionUniformizer l L ^ e})
    (hexp : index e n + 1 = e * (n + 1)) :
    Padic.coefficientExtensionRing l E (n + 1) →+*
      Padic.coefficientExtensionRing l L (index e n + 1) :=
  Ideal.Quotient.lift (Padic.coefficientExtensionIdeal l E (n + 1))
    ((Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (index e n + 1))).comp
      (integralScalarIntegerInclusion l E L ι)) (ramified_kernel l E L ι e n he hexp)

private theorem ramifiedQuotient_reduction (W : Scheme.{t}) (e n : ℕ)
    (he : Ideal.span ({integralScalarIntegerInclusion l E L ι
      (Padic.coefficientExtensionUniformizer l E)} :
        Set (Padic.coefficientExtensionIntegers l L)) =
      Ideal.span {Padic.coefficientExtensionUniformizer l L ^ e})
    (hexp : index e n + 1 = e * (n + 1)) (hn : n ≤ index e n)
    (U : W.ProEtᵒᵖ) (a : (integralCoefficientCommRingSheaf l E W n).obj.obj U) :
    (((integralCoefficientSheafSystem l L W).map (homOfLE hn).op).hom.app U)
        ((ramifiedMap l E L W e n (ramifiedQuotient l E L ι e n he hexp)).hom.app U a) =
      (integralScalarQuotientSheafMap l E L ι W n).hom.app U a := by
  let F := sheafCompose (Scheme.ProEt.topology W)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
  have h : F.map (ramifiedMap l E L W e n (ramifiedQuotient l E L ι e n he hexp)) ≫
      (integralCoefficientSheafSystem l L W).map (homOfLE hn).op =
        F.map (integralScalarQuotientSheafMap l E L ι W n) := by
    rw [AlgebraicGeometry.ProEtale.coefficientTower_map]
    change F.map _ ≫ F.map _ = F.map _
    rw [← Functor.map_comp]
    apply congrArg F.map
    unfold ramifiedMap constantMap integralScalarQuotientSheafMap
    rw [← Functor.map_comp]
    congr 1
    ext x
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x.down
    rcases x with ⟨x⟩
    dsimp only at ha
    subst x
    rfl
  exact congrArg (fun k ↦ k.hom.app U a) h

private theorem completedProjection_reduction (W : Scheme.{t}) (a b : ℕ) (h : a ≤ b)
    (U : W.ProEtᵒᵖ)
    (s : (completedIntegralCommRingSheafUnrestricted l L W).obj.obj U) :
    (((integralCoefficientSheafSystem l L W).map (homOfLE h).op).hom.app U)
        ((completedIntegralCommRingProjectionUnrestricted l L W b).hom.app U s) =
      (completedIntegralCommRingProjectionUnrestricted l L W a).hom.app U s :=
  congrArg (fun k ↦ k.hom.app U s)
    (limit.w (integralCoefficientSheafSystem l L W) (homOfLE h).op)

private def pullbackReduction {X Y : Scheme.{t}} (g : X ⟶ Y)
    (a b : ℕ) (h : a ≤ b) :
    integralOperationsPullbackLevel l L g b ⟶ integralOperationsPullbackLevel l L g a where
  app P := transition l L g a b h P
  naturality P Q f := by
    exact (((integralOperationsPullbackTowerFunctor l L g).map f).naturality
      (homOfLE h).op).symm

/-- The scalar-extended finite E-pullback tower is canonically the ramified
subsequence of the L-pullback tower, with the specified same-index factorization.
Source: Stacks 093M, 03EK and 03EL; Bhatt--Scholze, Lemma 6.8.2(1)
(blueprint: lem-weil-ramified-pullback-tower-identification).

Proof:
1. Use uniqueness of the extended absolute value and the local-field DVR factorization
   (lem-weil-l-adic-extension-absolute-value and -integers-dvr) to obtain the unique
   positive ramification exponent and equality of the principal-power ideals.
2. The same-index quotient maps give the completed map by its projections. At exponent
   em this factors through the E quotient of exponent m, giving j_m. Naturality of the
   constant coefficient maps gives compatibility with the geometric structure maps.
3. Apply the canonical quotient clause of lem-weil-pbc-constant-completion-equivalence
   (Stacks 093M) to both Noetherian valuation rings. The two ramified ideals agree.
4. The coefficient iso sends a⊗s to j_m(a)π_em(s); its inverse sends the residue of s
   to 1⊗s. Tensor balancing proves inverse identities locally, hence after sheafification.
5. Apply lem-weil-pbc-algebraic-inverse-image-tensor-comparison, with its adjunction
   and finite-limit hypotheses, to identify finite pullback with g⁻¹P⊗B_X.
6. Reassociate these balanced tensors on both sides, cancel the intermediate S_Y
   factor, and use Step 4. This gives the displayed pullback formula degreewise.
7. Quotient reduction commutes with j_m and with the actual limit projections.
   Apply those equations to the formula to prove the transition equation. Replacing
   p by f(p) proves naturality for every chain map.
8. Reduction from em to m sends j_m to iota_m and π_em to π_m, proving the specified
   same-index factorization. The subsequence is increasing and unbounded since e≥1.
9. No formula uses the unit in t=u*v^e; it is used only to prove equality of ideals.
   Thus the normalized maps are independent of that unit. -/
theorem identification {X Y : Scheme.{t}} (g : X ⟶ Y)
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    Nonempty (Identification l E L ι g) := by
  obtain ⟨e, he, hideal, huniq⟩ := ramification_exists l E L ι
  have hexp (n : ℕ) : index e n + 1 = e * (n + 1) := by
    have hp : 0 < e * (n + 1) := Nat.mul_pos he (by omega)
    dsimp [index]
    omega
  have hmono : Monotone (index e) := by
    intro a b hab
    exact Nat.sub_le_sub_right (Nat.mul_le_mul_left e (Nat.add_le_add_right hab 1)) 1
  have hsame (n : ℕ) : n ≤ index e n := by
    have hh := Nat.mul_le_mul_right (n + 1) he
    simp only [one_mul] at hh
    have hx := hexp n
    omega
  let j := fun n ↦ ramifiedQuotient l E L ι e n hideal (hexp n)
  have hj (n : ℕ) (a : Padic.coefficientExtensionIntegers l E) :
      j n (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a) =
        Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l L (index e n + 1))
          (integralScalarIntegerInclusion l E L ι a) := rfl
  obtain ⟨source⟩ := coefficients_exists l E L ι e he hideal hexp j hj Y
  obtain ⟨target⟩ := coefficients_exists l E L ι e he hideal hexp j hj X
  obtain ⟨d, hd, ht⟩ := finitePullbackComparison_exists l E L ι g e hmono j hj source target
  let same (n : ℕ) := (d n).hom ≫
    Functor.whiskerLeft (scalarCx source.completedMap)
      (pullbackReduction l L g n (index e n) (hsame n))
  refine ⟨{
    e := e
    positive := he
    ideal := hideal
    unique_index := huniq
    exponent := hexp
    monotone := hmono
    same_le := hsame
    quotientMap := j
    quotient_formula := hj
    source := source
    target := target
    levelIso := d
    pullback_formula := hd
    transitions := ht
    sameIndex := same
    same_formula := ?_
    factorization := fun _ _ ↦ rfl }⟩
  intro n P i V a b s p
  change ((transition l L g n (index e n) (hsame n)
    ((scalarCx source.completedMap).obj P)).f i).val.app _
      ((((d n).hom.app P).f i).val.app _
        (tensor target.completedMap _ _ s (pullTensor l E g n P i V a b p))) = _
  rw [hd, pullTensor_transition]
  rw [ramifiedQuotient_reduction l E L ι Y e n hideal (hexp n) (hsame n)]
  rw [map_mul, ramifiedQuotient_reduction l E L ι X e n hideal (hexp n) (hsame n),
    completedProjection_reduction l L X n (index e n) (hsame n)]

end WeilConjectures.RamifiedPullback
