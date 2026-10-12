/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineDifferentials
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TransitionUnits

/-!
# The twisting sheaves on the projective line are twisted structure sheaves

Let `S` be a scheme and `ℙ¹_S = ProjectiveLine S`, covered by the standard opens
`U₀ = D₊(x₀)` and `U₁ = D₊(x₁)`. A twisted structure sheaf `𝒪(d)` on `ℙ¹_S` is a module with
generators `g₀` on `U₀` and `g₁` on `U₁` glued by `g₀ = t^{-d} g₁` on `U₀ ∩ U₁`, `t = x₁ / x₀`
(`AlgebraicGeometry.ProjectiveLine.TwistData`). We show that the twisting sheaf
`AlgebraicGeometry.ProjectiveSpace.twist` is one, with generators the Laurent monomials
`x₀ᵈ` and `x₁ᵈ`, and that a twisted structure sheaf is unique up to unique isomorphism
compatible with the generators.

## Main definitions

- `AlgebraicGeometry.ProjectiveLine.twistData`: the twisted structure sheaf structure of `𝒪(d)`.

## Main statements

- `AlgebraicGeometry.ProjectiveLine.TwistData.existsUnique_iso`: uniqueness up to unique
  isomorphism compatible with the generators.
- `AlgebraicGeometry.ProjectiveLine.nonempty_twistData`: `𝒪(d)` exists, is invertible and is
  unique (blueprint `lem-sc-p1-twist-exists`).
-/

@[expose] public section

universe u

open CategoryTheory MvPolynomial HomogeneousLocalization

noncomputable section

namespace AlgebraicGeometry.ProjectiveLine

open ProjectiveSpace Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The index type `{0, 1}` of the homogeneous coordinates of `ℙ¹`. -/
local notation "T₂" => ULift (Fin 2)

/-- The index `0`. -/
local notation "j₀" => (⟨0⟩ : ULift (Fin 2))

/-- The index `1`. -/
local notation "j₁" => (⟨1⟩ : ULift (Fin 2))

variable (S : Scheme.{u})

/-- The standard open `D₊(xᵢ)` of `ℙ¹_S` is the open `⋂_{j ∈ {i}} D₊(xⱼ)` of the monomial
sections. -/
lemma standardOpen_le_preimage_basicOpenInt (i : ULift.{u} (Fin 2)) :
    standardOpen T₂ S i ≤ toProjInt T₂ S ⁻¹ᵁ basicOpenInt T₂ {i} := fun _ hx ↦
  Proj.mem_basicOpen_monomialToNat_indicator.2 fun _ hj ↦ by
    rw [Set.mem_singleton_iff.1 hj]
    exact hx

/-- The overlap `D₊(x₀) ∩ D₊(x₁)` of `ℙ¹_S` is the open `⋂_j D₊(xⱼ)` of the monomial sections. -/
lemma inf_le_preimage_basicOpenInt_univ :
    standardOpen T₂ S j₀ ⊓ standardOpen T₂ S j₁ ≤ toProjInt T₂ S ⁻¹ᵁ basicOpenInt T₂ Set.univ :=
  fun _ hx ↦ Proj.mem_basicOpen_monomialToNat_indicator.2 fun j _ ↦ by
    rcases eq_or_eq_of_ne (i := j₀) (j := j₁) (by decide) j with rfl | rfl
    exacts [hx.1, hx.2]

/-- The generator `xᵢᵈ` of `𝒪(d)` on the standard open `D₊(xᵢ)` of `ℙ¹_S`. -/
def twistGenerator (d : ℤ) (i : ULift.{u} (Fin 2)) : Γ(twist T₂ S d, standardOpen T₂ S i) :=
  (twist T₂ S d).presheaf.map (homOfLE (standardOpen_le_preimage_basicOpenInt S i)).op
    (twistMonomialSection S {i} (Proj.singleExponent (s := {i}) (m := d) (Set.mem_singleton i)))

lemma isFreeGenerator_twistGenerator (d : ℤ) (i : ULift.{u} (Fin 2)) :
    IsFreeGenerator (twistGenerator S d i) :=
  (isFreeGenerator_twistMonomialSection_singleExponent _).map _

/-- The exponent vector `d (e₀ - e₁)` of the Laurent monomial `(x₀ / x₁)ᵈ`. -/
def ratioExponent (d : ℤ) : laurentExponents (Set.univ : Set (ULift.{u} (Fin 2))) 0 :=
  ⟨d • (Pi.single (⟨0⟩ : ULift.{u} (Fin 2)) 1 - Pi.single ⟨1⟩ 1), by
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, ← Finset.mul_sum, Finset.sum_sub_distrib,
      Finset.sum_pi_single', Finset.mem_univ, if_true, sub_self, mul_zero],
    fun _ hi ↦ (hi trivial).elim⟩

lemma awayMonomial_ratioExponent_mul (a b : ℤ) :
    awayMonomial (ULift.{u} ℤ) Set.univ (ratioExponent.{u} a) *
        awayMonomial (ULift.{u} ℤ) Set.univ (ratioExponent.{u} b) =
      awayMonomial (ULift.{u} ℤ) Set.univ (ratioExponent.{u} (a + b)) :=
  Proj.awayMonomial_mul (R := ULift.{u} ℤ) _ _ _ (add_smul a b _)

lemma awayMonomial_ratioExponent_zero :
    awayMonomial (ULift.{u} ℤ) Set.univ (ratioExponent.{u} 0) = 1 :=
  Proj.awayMonomial_zero (R := ULift.{u} ℤ) _ (zero_smul ℤ _)

/-- The unit `x₀ / x₁` of the degree-zero localization of `ℤ[x₀, x₁]` away from `x₀ x₁`. -/
def ratioAwayUnit : (Away (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
    (monomialToNat (ULift.{u} ℤ) ((Set.univ : Set (ULift.{u} (Fin 2))).indicator 1)))ˣ where
  val := awayMonomial (ULift.{u} ℤ) Set.univ (ratioExponent.{u} 1)
  inv := awayMonomial (ULift.{u} ℤ) Set.univ (ratioExponent.{u} (-1))
  val_inv := by rw [awayMonomial_ratioExponent_mul, add_neg_cancel, awayMonomial_ratioExponent_zero]
  inv_val := by rw [awayMonomial_ratioExponent_mul, neg_add_cancel, awayMonomial_ratioExponent_zero]

lemma awayMonomial_ratioExponent (d : ℤ) :
    awayMonomial (ULift.{u} ℤ) Set.univ (ratioExponent.{u} d) = ((ratioAwayUnit ^ d : _ˣ) : _) := by
  induction d using Int.induction_on with
  | zero => rw [zpow_zero, Units.val_one, awayMonomial_ratioExponent_zero]
  | succ d ih =>
    rw [← awayMonomial_ratioExponent_mul, ih, zpow_add_one, Units.val_mul]
    rfl
  | pred d ih =>
    rw [show -(d : ℤ) - 1 = -d + -1 by ring, ← awayMonomial_ratioExponent_mul, ih, zpow_add,
      zpow_neg_one, Units.val_mul]
    rfl

/-- The functions on `D₊(x₀) ∩ D₊(x₁) ⊆ ℙ¹_S` coming from the degree-zero localization of
`ℤ[x₀, x₁]` away from `x₀ x₁`. -/
def overlapFun : Away (homogeneousSubmodule (ULift.{u} (Fin 2)) (ULift.{u} ℤ))
      (monomialToNat (ULift.{u} ℤ) ((Set.univ : Set (ULift.{u} (Fin 2))).indicator 1)) →+*
      Γ(ProjectiveLine S, standardOpen T₂ S j₀ ⊓ standardOpen T₂ S j₁) :=
  (Proj.awayToSection _ _ ≫ (toProjInt T₂ S).appLE (basicOpenInt T₂ Set.univ)
    (standardOpen T₂ S j₀ ⊓ standardOpen T₂ S j₁) (inf_le_preimage_basicOpenInt_univ S)).hom

lemma monomialToNat_indicator_univ :
    monomialToNat (ULift.{u} ℤ) ((Set.univ : Set (ULift.{u} (Fin 2))).indicator 1) =
      X ⟨1⟩ * X ⟨0⟩ := by
  rw [monomialToNat_eq_prod, ← Equiv.ulift.symm.prod_comp, Fin.prod_univ_two]
  simp [mul_comm]

lemma overlapFun_awayMonomial_ratioExponent_one :
    overlapFun S (awayMonomial (ULift.{u} ℤ) Set.univ (ratioExponent.{u} 1)) =
      ratio T₂ S j₀ j₁ := by
  have h := map_ratio (S := S) (i := j₀) (X_mem_homogeneousSubmodule_one _ j₀)
    (monomialToNat_indicator_univ) (inf_le_preimage_basicOpenInt_univ S) le_rfl
  rw [show (homOfLE (le_refl (standardOpen T₂ S j₀ ⊓ standardOpen T₂ S j₁))) = 𝟙 _ from rfl,
    op_id, CategoryTheory.Functor.map_id, CommRingCat.id_apply] at h
  rw [h]
  refine appLE_awayToSection_congr _ ?_
  have hN : ∀ i, -(ratioExponent.{u} 1).1 i ≤ (1 : ℕ) := fun i ↦ by
    simp only [ratioExponent, one_smul, Pi.sub_apply, Pi.single_apply]
    split_ifs <;> simp
  rw [← awayMonomial_eq _ hN, Away.val_mk, val_awayMap_awayRatio]
  have h0 := indicator_one_nonneg (Set.univ : Set (ULift.{u} (Fin 2)))
  refine mk_eq_mk_of_monomialToNat (add_nsmul_indicator_nonneg (fun _ hi ↦ (hi trivial).elim) hN)
    (nsmul_nonneg h0 1) (a' := Pi.single j₀ 2) (b' := Set.univ.indicator 1) ?_ h0 rfl
    (by simp) ?_ (by rw [monomialToNat_indicator_univ]) ?_
  · intro i
    simp only [Pi.single_apply, Pi.zero_apply]
    split_ifs <;> simp
  · rw [monomialToNat_eq_prod, ← Equiv.ulift.symm.prod_comp, Fin.prod_univ_two]
    simp [sq]
  · rw [Set.indicator_univ, one_smul]
    funext i
    obtain ⟨⟨i, hi⟩⟩ := i
    simp only [ratioExponent, one_smul, Pi.add_apply, Pi.sub_apply, Pi.single_apply,
      Pi.one_apply]
    interval_cases i <;> simp [Set.indicator, Membership.mem, Set.Mem]

lemma overlapFun_awayMonomial_ratioExponent (d : ℤ) :
    overlapFun S (awayMonomial (ULift.{u} ℤ) Set.univ (ratioExponent.{u} d)) =
      (transitionUnit T₂ S d j₀ j₁).1 := by
  have hu : Units.map (overlapFun S).toMonoidHom ratioAwayUnit = ratioUnit T₂ S j₀ j₁ :=
    Units.ext (overlapFun_awayMonomial_ratioExponent_one S)
  rw [awayMonomial_ratioExponent, transitionUnit, ← hu, ← map_zpow]
  rfl

/-- **The glueing relation for the generators of `𝒪(d)`**: `x₀ᵈ = (x₀ / x₁)ᵈ x₁ᵈ` on
`D₊(x₀) ∩ D₊(x₁)`. -/
lemma twistGenerator_map (d : ℤ) :
    (twist T₂ S d).presheaf.map (homOfLE inf_le_left).op (twistGenerator S d j₀) =
      (transitionUnit T₂ S d j₀ j₁).1 •
        (twist T₂ S d).presheaf.map (homOfLE inf_le_right).op (twistGenerator S d j₁) := by
  have hW := inf_le_preimage_basicOpenInt_univ S
  have h₀ := twist_presheaf_map_twistMonomialSection (S := S) (m := d)
    (Set.subset_univ {j₀}) (Proj.singleExponent (s := {j₀}) (m := d) (Set.mem_singleton _))
  have h₁ := twist_presheaf_map_twistMonomialSection (S := S) (m := d)
    (Set.subset_univ {j₁}) (Proj.singleExponent (s := {j₁}) (m := d) (Set.mem_singleton _))
  have hU (i : ULift.{u} (Fin 2)) : toProjInt T₂ S ⁻¹ᵁ basicOpenInt T₂ Set.univ ≤
      toProjInt T₂ S ⁻¹ᵁ basicOpenInt T₂ {i} :=
    (toProjInt T₂ S).preimage_mono (Proj.basicOpen_monomialToNat_indicator_mono
      (R := ULift.{u} ℤ) (Set.subset_univ {i}))
  have L₀ : (twist T₂ S d).presheaf.map (homOfLE inf_le_left).op (twistGenerator S d j₀) =
      (twist T₂ S d).presheaf.map (homOfLE hW).op ((twist T₂ S d).presheaf.map (homOfLE (hU j₀)).op
        (twistMonomialSection S {j₀}
          (Proj.singleExponent (s := {j₀}) (m := d) (Set.mem_singleton _)))) := by
    rw [twistGenerator, presheaf_map_homOfLE_map_homOfLE, presheaf_map_homOfLE_map_homOfLE]
  have L₁ : (twist T₂ S d).presheaf.map (homOfLE inf_le_right).op (twistGenerator S d j₁) =
      (twist T₂ S d).presheaf.map (homOfLE hW).op ((twist T₂ S d).presheaf.map (homOfLE (hU j₁)).op
        (twistMonomialSection S {j₁}
          (Proj.singleExponent (s := {j₁}) (m := d) (Set.mem_singleton _)))) := by
    rw [twistGenerator, presheaf_map_homOfLE_map_homOfLE, presheaf_map_homOfLE_map_homOfLE]
  rw [L₀, L₁, h₀, h₁]
  conv_lhs => rw [twistMonomialSection_eq_smul (Set.mem_univ j₁), map_smul]
  congr 1
  · rw [← overlapFun_awayMonomial_ratioExponent, ← ConcreteCategory.comp_apply,
      Category.assoc, Scheme.Hom.appLE_map, overlapFun]
    congr 2
    refine Subtype.ext (funext fun i ↦ ?_)
    obtain ⟨⟨i, hi⟩⟩ := i
    simp only [Proj.shiftExponent, Proj.singleExponent, ratioExponent, Pi.sub_apply,
      Pi.single_apply, Pi.smul_apply, smul_eq_mul]
    interval_cases i <;> simp

/-- **`𝒪(d)` is a twisted structure sheaf** on `ℙ¹_S`, with generators the Laurent monomials
`x₀ᵈ` on `D₊(x₀)` and `x₁ᵈ` on `D₊(x₁)`. -/
def twistData (d : ℤ) : TwistData S d (twist T₂ S d) where
  g₀ := twistGenerator S d j₀
  g₁ := twistGenerator S d j₁
  bijective_smul_g₀ := isFreeGenerator_twistGenerator S d j₀
  bijective_smul_g₁ := isFreeGenerator_twistGenerator S d j₁
  map_g₀ := twistGenerator_map S d

namespace TwistData

variable {S} {d : ℤ} {𝓛 𝓛' : (ProjectiveLine S).Modules}

/-- The generators of a twisted structure sheaf, indexed by `Fin 2`. -/
def gen (D : TwistData S d 𝓛) : (i : Fin 2) → Γ(𝓛, standardOpen T₂ S ⟨i⟩)
  | 0 => D.g₀
  | 1 => D.g₁

lemma isFreeGenerator_gen (D : TwistData S d 𝓛) : ∀ i : Fin 2, IsFreeGenerator (D.gen i)
  | 0 => D.bijective_smul_g₀
  | 1 => D.bijective_smul_g₁

variable (S) in
lemma iSup_standardOpen_up : ⨆ i : Fin 2, standardOpen T₂ S ⟨i⟩ = ⊤ :=
  (Equiv.ulift.symm.iSup_comp (g := fun i ↦ standardOpen T₂ S i)).trans
    (iSup_standardOpen T₂ S)

/-- The glueing relation `g₀ = u₀₁ g₁` restricted to an open `W ⊆ U₀ ∩ U₁`. -/
lemma map_g₀_eq (D : TwistData S d 𝓛) {W : (ProjectiveLine S).Opens}
    (h₀ : W ≤ standardOpen T₂ S j₀) (h₁ : W ≤ standardOpen T₂ S j₁) :
    𝓛.presheaf.map (homOfLE h₀).op D.g₀ =
      (ProjectiveLine S).presheaf.map (homOfLE (le_inf h₀ h₁)).op
          (transitionUnit T₂ S d j₀ j₁).1 •
        𝓛.presheaf.map (homOfLE h₁).op D.g₁ := by
  rw [← presheaf_map_homOfLE_map_homOfLE inf_le_left (le_inf h₀ h₁), D.map_g₀, map_smul,
    presheaf_map_homOfLE_map_homOfLE]

/-- On an open `W ⊆ Uᵢ ∩ Uⱼ`, the relations between the generators `gᵢ`, `gⱼ` of two twisted
structure sheaves of the same degree are the same. -/
lemma smul_gen_eq (D : TwistData S d 𝓛) (D' : TwistData S d 𝓛') :
    ∀ (i j : Fin 2) (W : (ProjectiveLine S).Opens) (hi : W ≤ standardOpen T₂ S ⟨i⟩)
      (hj : W ≤ standardOpen T₂ S ⟨j⟩) (a b : Γ(ProjectiveLine S, W)),
      a • 𝓛.presheaf.map (homOfLE hi).op (D.gen i) =
        b • 𝓛.presheaf.map (homOfLE hj).op (D.gen j) →
      a • 𝓛'.presheaf.map (homOfLE hi).op (D'.gen i) =
        b • 𝓛'.presheaf.map (homOfLE hj).op (D'.gen j)
  | 0, 0, _, hi, _, a, b, h => by
    obtain rfl : a = b := ((D.isFreeGenerator_gen 0).map hi).smul_left_injective h
    rfl
  | 0, 1, _, hi, hj, a, b, h => by
    change a • 𝓛.presheaf.map (homOfLE hi).op D.g₀ = b • 𝓛.presheaf.map (homOfLE hj).op D.g₁
      at h
    change a • 𝓛'.presheaf.map (homOfLE hi).op D'.g₀ = b • 𝓛'.presheaf.map (homOfLE hj).op D'.g₁
    rw [D.map_g₀_eq hi hj, smul_smul] at h
    rw [D'.map_g₀_eq hi hj, smul_smul, ((D.isFreeGenerator_gen 1).map hj).smul_left_injective h]
  | 1, 0, _, hi, hj, a, b, h => by
    change a • 𝓛.presheaf.map (homOfLE hi).op D.g₁ = b • 𝓛.presheaf.map (homOfLE hj).op D.g₀
      at h
    change a • 𝓛'.presheaf.map (homOfLE hi).op D'.g₁ = b • 𝓛'.presheaf.map (homOfLE hj).op D'.g₀
    rw [D.map_g₀_eq hj hi, smul_smul] at h
    rw [D'.map_g₀_eq hj hi, smul_smul, ((D.isFreeGenerator_gen 1).map hi).smul_left_injective h]
  | 1, 1, _, hi, _, a, b, h => by
    obtain rfl : a = b := ((D.isFreeGenerator_gen 1).map hi).smul_left_injective h
    rfl

/-- The morphism of twisted structure sheaves of the same degree sending generators to
generators. -/
def hom (D : TwistData S d 𝓛) (D' : TwistData S d 𝓛') : 𝓛 ⟶ 𝓛' :=
  glueHom (iSup_standardOpen_up S) D.isFreeGenerator_gen (smul_gen_eq D D')

lemma hom_app_gen (D : TwistData S d 𝓛) (D' : TwistData S d 𝓛') (i : Fin 2) :
    (D.hom D').app _ (D.gen i) = D'.gen i :=
  glueHom_app_self _ _ _ i

lemma hom_ext' (D : TwistData S d 𝓛) {φ ψ : 𝓛 ⟶ 𝓛'} (h₀ : φ.app _ D.g₀ = ψ.app _ D.g₀)
    (h₁ : φ.app _ D.g₁ = ψ.app _ D.g₁) : φ = ψ :=
  hom_ext_of_isFreeGenerator (iSup_standardOpen_up S) D.isFreeGenerator_gen fun
    | 0 => h₀
    | 1 => h₁

/-- **Uniqueness of twisted structure sheaves.** Two twisted structure sheaves of the same
degree `d` on `ℙ¹_S` are isomorphic by a unique isomorphism sending the generators `g₀`, `g₁`
of the first to those of the second. -/
theorem existsUnique_iso (D : TwistData S d 𝓛) (D' : TwistData S d 𝓛') :
    ∃! φ : 𝓛 ≅ 𝓛', φ.hom.app _ D.g₀ = D'.g₀ ∧ φ.hom.app _ D.g₁ = D'.g₁ := by
  refine ⟨⟨D.hom D', D'.hom D, D.hom_ext' ?_ ?_, D'.hom_ext' ?_ ?_⟩,
    ⟨D.hom_app_gen D' 0, D.hom_app_gen D' 1⟩, fun φ hφ ↦ Iso.ext (D.hom_ext' ?_ ?_)⟩
  · rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
    erw [D.hom_app_gen D' 0, D'.hom_app_gen D 0]
    rfl
  · rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
    erw [D.hom_app_gen D' 1, D'.hom_app_gen D 1]
    rfl
  · rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
    erw [D'.hom_app_gen D 0, D.hom_app_gen D' 0]
    rfl
  · rw [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
    erw [D'.hom_app_gen D 1, D.hom_app_gen D' 1]
    rfl
  · exact hφ.1.trans (D.hom_app_gen D' 0).symm
  · exact hφ.2.trans (D.hom_app_gen D' 1).symm

end TwistData

/-- **The twists `𝒪(d)` exist.** For every `d ∈ ℤ`, a twisted structure sheaf `𝒪(d)` on `ℙ¹_S`
in the sense of `AlgebraicGeometry.ProjectiveLine.TwistData` (generators `g₀` on `U₀`, `g₁` on
`U₁`, glued by `g₀ = t^{-d} g₁`) exists, namely the twisting sheaf
`AlgebraicGeometry.ProjectiveSpace.twist` (`AlgebraicGeometry.ProjectiveLine.twistData`); it is
an invertible module; and it is unique up to unique isomorphism compatible with the generators
(`AlgebraicGeometry.ProjectiveLine.TwistData.existsUnique_iso`).

The blueprint states this for `S = Spec k`, `k` a field.

(blueprint: `lem-sc-p1-twist-exists`, `rem-ptr-sc-p1-standard-5`) -/
theorem nonempty_twistData (d : ℤ) :
    Nonempty (TwistData S d (twist T₂ S d)) ∧ (twist T₂ S d).IsInvertible ∧
      ∀ {𝓛 𝓛' : (ProjectiveLine S).Modules} (D : TwistData S d 𝓛) (D' : TwistData S d 𝓛'),
        ∃! φ : 𝓛 ≅ 𝓛', φ.hom.app _ D.g₀ = D'.g₀ ∧ φ.hom.app _ D.g₁ = D'.g₁ :=
  ⟨⟨twistData S d⟩, inferInstance, fun D D' ↦ D.existsUnique_iso D'⟩

end AlgebraicGeometry.ProjectiveLine
