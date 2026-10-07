/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import WeilConjectures.Mathlib.RingTheory.Spectrum.Prime.Noetherian

/-!
# Fibres of finite flat morphisms

A fibre of a finite flat morphism `f : X ⟶ Y` over a point `y` has at most
`Scheme.Hom.finrank f y` points, and a morphism out of the empty scheme has rank `0` everywhere.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.ncard_preimage_singleton_le_finrank`: a fibre of a finite flat
  morphism over `y` has at most `f.finrank y` points.
- `AlgebraicGeometry.Scheme.Hom.finrank_eq_zero_of_isEmpty`: a morphism out of an empty scheme
  has rank `0` everywhere.
-/

@[expose] public section

universe u

open CategoryTheory Limits


/-- Over a maximal ideal `P` of `B`, the dimension of `C ⊗ B ⧸ P` over `B ⧸ P` is the rank of
`C` at `P`. -/
lemma Module.finrank_quotient_tensorProduct_eq_rankAtStalk {B C : Type*} [CommRing B]
    [AddCommGroup C] [Module B C] [Module.Finite B C] [Module.Flat B C] (P : Ideal B)
    [P.IsMaximal] :
    Module.finrank (B ⧸ P) (TensorProduct B (B ⧸ P) C) =
      Module.rankAtStalk C ⟨P, inferInstance⟩ := by
  let := Ideal.Quotient.field P
  rw [Module.rankAtStalk_eq, ← (TensorProduct.AlgebraTensorModule.cancelBaseChange B (B ⧸ P)
    P.ResidueField P.ResidueField C).finrank_eq]
  exact (Module.finrank_baseChange (R := P.ResidueField) (S := B ⧸ P)).symm

/-- **The rank is multiplicative, over a field.** Let `K ⟶ B ⟶ C` be finite, with `C` flat over
`B` of constant rank `n`. Then `[C : K] = n [B : K]`: the ring `B` is artinian, hence semilocal,
so that `C` is a free `B`-module of rank `n`. -/
theorem Module.finrank_eq_mul_of_rankAtStalk_eq {K B C : Type*} [Field K] [CommRing B]
    [CommRing C] [Algebra K B] [Algebra B C] [Algebra K C] [IsScalarTower K B C]
    [Module.Finite K B] [Module.Finite B C] [Module.Flat B C] {n : ℕ}
    (h : ∀ q, Module.rankAtStalk (R := B) C q = n) :
    Module.finrank K C = n * Module.finrank K B := by
  rcases subsingleton_or_nontrivial B with hB | hB
  · have : Subsingleton C := Module.subsingleton B C
    simp [Module.finrank_zero_of_subsingleton]
  have : IsArtinianRing B := IsArtinianRing.of_finite K B
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq B C n fun P ↦ by
    rw [Module.finrank_quotient_tensorProduct_eq_rankAtStalk, h]
  have : Module.Free B C := .of_basis b
  rw [← Module.finrank_mul_finrank K B C, Module.finrank_eq_card_basis b, Fintype.card_fin,
    mul_comm]

namespace AlgebraicGeometry

/-- A morphism out of an empty scheme has rank `0` everywhere. -/
lemma Scheme.Hom.finrank_eq_zero_of_isEmpty {Z T : Scheme.{u}} (g : Z ⟶ T) [IsEmpty Z]
    (t : T) : g.finrank t = 0 := by
  obtain ⟨R, i, _, y, rfl⟩ := T.exists_Spec_apply_eq t
  rw [← Scheme.Hom.finrank_pullback_snd]
  have : IsEmpty ↥(pullback g i) := Function.isEmpty (pullback.fst g i)
  let φ : R ⟶ CommRingCat.of PUnit.{u + 1} := CommRingCat.punitIsTerminal.from R
  have e : pullback.snd g i = isInitialOfIsEmpty.to (Spec (CommRingCat.of PUnit.{u + 1})) ≫
      Spec.map φ := isInitialOfIsEmpty.hom_ext _ _
  rw [e, finrank_comp_left_of_isIso,
    finrank_SpecMap_eq_finrank ((IsFinite.SpecMap_iff φ).mp inferInstance)
      (Flat.SpecMap_iff.mp inferInstance)]
  let := φ.hom.toAlgebra
  exact congrFun Module.rankAtStalk_eq_zero_of_subsingleton y

/-- A scheme which is finite and flat over the spectrum of a field `K` is finite, with at most
as many points as the rank. -/
lemma Scheme.Hom.finite_and_card_le_finrank_of_field {K : Type u} [Field K]
    {Z : Scheme.{u}} (g : Z ⟶ Spec (.of K)) [IsFinite g] [Flat g] (z : Spec (.of K)) :
    Finite Z ∧ Nat.card Z ≤ g.finrank z := by
  have : IsAffine Z := isAffine_of_isAffineHom g
  let e := Scheme.homeoOfIso Z.isoSpec
  rw [← finrank_comp_left_of_isIso Z.isoSpec.inv, Nat.card_congr e.toEquiv,
    e.toEquiv.finite_iff]
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (Z.isoSpec.inv ≫ g)
  have h₁ : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  have h₂ : φ.hom.Flat := by
    rw [← Flat.SpecMap_iff, hφ]
    infer_instance
  rw [← hφ, finrank_SpecMap_eq_finrank h₁ h₂]
  algebraize [φ.hom]
  have : IsArtinianRing Γ(Z, ⊤) := .of_finite K Γ(Z, ⊤)
  rw [← RingHom.algebraMap_toAlgebra φ.hom, RingHom.finrank_algebraMap,
    Module.rankAtStalk_eq_finrank_of_free]
  exact ⟨inferInstanceAs (Finite (PrimeSpectrum Γ(Z, ⊤))),
    IsArtinianRing.card_primeSpectrum_le_finrank K Γ(Z, ⊤)⟩

instance {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (y : Y) :
    IsFinite (f.fiberToSpecResidueField y) :=
  inferInstanceAs (IsFinite (pullback.snd f (Y.fromSpecResidueField y)))

instance {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (y : Y) :
    Flat (f.fiberToSpecResidueField y) :=
  inferInstanceAs (Flat (pullback.snd f (Y.fromSpecResidueField y)))

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [Flat f]

/-- A fibre of a finite flat morphism `f` over `y` has at most `f.finrank y` points: it is the
spectrum of an algebra of dimension `f.finrank y` over the residue field of `y`. -/
lemma Scheme.Hom.ncard_preimage_singleton_le_finrank (y : Y) :
    (f ⁻¹' {y}).ncard ≤ f.finrank y := by
  have h := (finite_and_card_le_finrank_of_field (K := Y.residueField y)
    (f.fiberToSpecResidueField y) (IsLocalRing.closedPoint _)).2
  rw [← Nat.card_coe_set_eq, ← Nat.card_congr (f.fiberHomeo y).toEquiv]
  exact h.trans_eq ((finrank_pullback_snd f (Y.fromSpecResidueField y) _).trans
    (congrArg f.finrank (Y.fromSpecResidueField_apply y _)))

/-- Composing with an isomorphism on the target does not change the rank. -/
lemma Scheme.Hom.finrank_comp_of_isIso_right {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (e : Y ⟶ Y')
    [IsIso e] [IsFinite f] [Flat f] (y : Y) : (f ≫ e).finrank (e y) = f.finrank y := by
  have h : IsPullback (𝟙 X) (f ≫ e) f (inv e) := IsPullback.of_horiz_isIso ⟨by simp⟩
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ h, ← Scheme.Hom.comp_apply, IsIso.hom_inv_id]
  rfl

/-- **The rank is multiplicative, over the spectrum of a field.** -/
theorem Scheme.Hom.finrank_comp_of_forall_finrank_eq_of_field {K : Type u} [Field K]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Spec (.of K)) [IsFinite f] [Flat f] [IsFinite g]
    [Flat g] {n : ℕ} (hf : ∀ y, f.finrank y = n) (z : Spec (.of K)) :
    (f ≫ g).finrank z = n * g.finrank z := by
  have : IsAffine Y := isAffine_of_isAffineHom g
  have : IsAffine X := isAffine_of_isAffineHom f
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.isoSpec.inv ≫ f ≫ Y.isoSpec.hom)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (Y.isoSpec.inv ≫ g)
  have hfg : f ≫ g = X.isoSpec.hom ≫ Spec.map φ ≫ Spec.map ψ := by simp [hφ, hψ]
  have hφf (y : _) : (Spec.map φ).finrank y = n := by
    have hy : Y.isoSpec.hom (Y.isoSpec.inv y) = y := by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      rfl
    rw [hφ, Scheme.Hom.finrank_comp_left_of_isIso, ← hy, Scheme.Hom.finrank_comp_of_isIso_right,
      hf]
  have hφ₁ : φ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hφ]
    infer_instance
  have hφ₂ : φ.hom.Flat := by
    rw [← Flat.SpecMap_iff, hφ]
    infer_instance
  have hψ₁ : ψ.hom.Finite := by
    rw [← IsFinite.SpecMap_iff, hψ]
    infer_instance
  have hψ₂ : ψ.hom.Flat := by
    rw [← Flat.SpecMap_iff, hψ]
    infer_instance
  have hφψ₁ : (ψ ≫ φ).hom.Finite := by
    rw [CommRingCat.hom_comp]
    exact hφ₁.comp hψ₁
  have hφψ₂ : (ψ ≫ φ).hom.Flat := by
    rw [CommRingCat.hom_comp]
    exact hψ₂.comp hφ₂
  have : IsFinite (Spec.map φ) := by
    rw [IsFinite.SpecMap_iff]
    exact hφ₁
  have : Flat (Spec.map φ) := Flat.SpecMap_iff.mpr hφ₂
  have : IsFinite (Spec.map ψ) := by
    rw [IsFinite.SpecMap_iff]
    exact hψ₁
  have : Flat (Spec.map ψ) := Flat.SpecMap_iff.mpr hψ₂
  rw [hfg, Scheme.Hom.finrank_comp_left_of_isIso, ← Scheme.Hom.finrank_comp_left_of_isIso
    Y.isoSpec.inv g, ← hψ, ← Spec.map_comp, Scheme.Hom.finrank_SpecMap_eq_finrank hψ₁ hψ₂,
    Scheme.Hom.finrank_SpecMap_eq_finrank hφψ₁ hφψ₂]
  simp only [Scheme.Hom.finrank_SpecMap_eq_finrank hφ₁ hφ₂] at hφf
  rw [CommRingCat.hom_comp]
  algebraize [ψ.hom, φ.hom, φ.hom.comp ψ.hom]
  rw [← RingHom.algebraMap_toAlgebra (φ.hom.comp ψ.hom), ← RingHom.algebraMap_toAlgebra ψ.hom,
    RingHom.finrank_algebraMap, RingHom.finrank_algebraMap,
    Module.rankAtStalk_eq_finrank_of_free, Module.rankAtStalk_eq_finrank_of_free]
  refine Module.finrank_eq_mul_of_rankAtStalk_eq fun q ↦ ?_
  rw [← hφf q, ← RingHom.algebraMap_toAlgebra φ.hom, RingHom.finrank_algebraMap]

/-- **The rank is multiplicative.** If `f : X ⟶ Y` and `g : Y ⟶ Z` are finite and flat and `f`
has constant rank `n`, then the rank of `f ≫ g` at `z` is `n` times the rank of `g` at `z`.

After base change to the residue field of `z`, this is
`AlgebraicGeometry.Scheme.Hom.finrank_comp_of_forall_finrank_eq_of_field`. -/
theorem Scheme.Hom.finrank_comp_of_forall_finrank_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) [IsFinite f] [Flat f] [IsFinite g] [Flat g] {n : ℕ}
    (hf : ∀ y, f.finrank y = n) (z : Z) :
    (f ≫ g).finrank z = n * g.finrank z := by
  let s := Z.fromSpecResidueField z
  let t : Spec (Z.residueField z) := IsLocalRing.closedPoint _
  have hs : s t = z := Z.fromSpecResidueField_apply z t
  have e : pullback.snd (f ≫ g) s = (pullbackRightPullbackFstIso g s f).inv ≫
      pullback.snd f (pullback.fst g s) ≫ pullback.snd g s := by simp
  rw [← hs, ← Scheme.Hom.finrank_pullback_snd (f ≫ g) s, ← Scheme.Hom.finrank_pullback_snd g s, e,
    Scheme.Hom.finrank_comp_left_of_isIso]
  exact Scheme.Hom.finrank_comp_of_forall_finrank_eq_of_field (K := Z.residueField z) _ _
    (fun y ↦ by rw [Scheme.Hom.finrank_pullback_snd, hf]) t

end AlgebraicGeometry
