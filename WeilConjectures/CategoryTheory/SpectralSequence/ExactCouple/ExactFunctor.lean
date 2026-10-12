/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.SpectralSequence.ExactCouple.DerivedFunctor
public import WeilConjectures.CategoryTheory.SpectralSequence.ExactCouple.Convergence
public import WeilConjectures.CategoryTheory.SpectralSequence.ExactCouple.DifferentialSubobjects
public import WeilConjectures.Mathlib.Algebra.Homology.SingleHomology

/-!
# Exact functors carry exact couples and their spectral sequences

Let `Φ : C ⥤ D` be an exact functor between abelian categories and `X = (D, E, α, f, g)` an
exact couple in `C`. Then:

* `X.mapExact Φ = (Φ D, Φ E, Φ α, Φ f, Φ g)` is an exact couple in `D`;
* applying `Φ` commutes with taking derived couples: there is an isomorphism of exact couples
  `Φ (X') ≅ (Φ X)'` (`CategoryTheory.ExactCouple.mapExactDerivedIso`), which is the comparison
  `Φ (ker g) ≅ ker (Φ g)` on `D`-terms and the comparison `θ : Φ (ker d / im d) ≅ ker Φd / im Φd`
  on `E`-terms; hence isomorphisms `Φ (C_r) ≅ (Φ C)_r` of all the iterated couples
  (`CategoryTheory.ExactCouple.mapExactIterIso`), compatible with the inclusions of the
  `D`-terms (`CategoryTheory.ExactCouple.mapExactIterIso_hom_hD_map_ιIter`) and with the
  differentials;
* if `X` is a half-plane couple, so is `X.mapExact Φ`, its abutment filtration is the image under
  `Φ` of that of `X` (`CategoryTheory.ExactCouple.mapExact_abutmentFiltration_F`), and the
  isomorphisms `ψ_r : grᵖ A^{p+q} ≅ E_r^{p,q}` of `thm-sp-half-plane-convergence` are carried by
  `Φ` to those of `X.mapExact Φ` (`CategoryTheory.ExactCouple.IsHalfPlane.mapExact_grIsoIterE`).

This is blueprint `lem-sp-exact-functor-couple`.
-/

@[expose] public section

namespace CategoryTheory

open Category Limits

variable {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]
  (Φ : C ⥤ D) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]

/-- Blueprint `lem-sp-exact-functor-preserves-homology` (c): an exact functor between abelian
categories preserves homology (`CategoryTheory.Functor.preservesHomologyOfExact`); in particular
it carries exact sequences to exact sequences. -/
lemma Functor.exact_map_of_exact {S : ShortComplex C} (hS : S.Exact) : (S.map Φ).Exact :=
  hS.map Φ

/-- Blueprint `lem-sp-exact-functor-preserves-homology` (b): an exact functor carries image
factorizations to image factorizations, i.e. `im (Φ u) = Φ (im u)` as subobjects of `Φ Y`. -/
lemma Functor.imageSubobject_map_arrow {X Y : C} (u : X ⟶ Y) :
    imageSubobject (Φ.map (imageSubobject u).arrow) = imageSubobject (Φ.map u) := by
  conv_rhs => rw [← imageSubobject_arrow_comp u, Φ.map_comp]
  exact (ExactCouple.imageSubobject_epi_comp (Φ.map (factorThruImageSubobject u)) _).symm

lemma Functor.imageSubobject_map_arrow_congr {Y : C} {S T : Subobject Y} (h : S = T) :
    imageSubobject (Φ.map S.arrow) = imageSubobject (Φ.map T.arrow) := by
  subst h
  rfl

namespace ExactCouple

section

variable {s : ℕ}

/-- A morphism of exact couples all of whose components are isomorphisms is an isomorphism. -/
lemma Hom.isIso_of_isIso {X Y : ExactCouple C s} (φ : X ⟶ Y) [∀ p q, IsIso (φ.hD p q)]
    [∀ p q, IsIso (φ.hE p q)] : IsIso φ := by
  let ψ : Y ⟶ X :=
    { hD p q := inv (φ.hD p q)
      hE p q := inv (φ.hE p q)
      comm_α p q p' q' hp hq := by
        rw [IsIso.eq_inv_comp, ← φ.comm_α_assoc p q p' q' hp hq, IsIso.hom_inv_id, comp_id]
      comm_f p q p' q' hp hq := by
        rw [IsIso.eq_inv_comp, ← φ.comm_f_assoc p q p' q' hp hq, IsIso.hom_inv_id, comp_id]
      comm_g p q p' q' hp hq := by
        rw [IsIso.eq_inv_comp, ← φ.comm_g_assoc p q p' q' hp hq, IsIso.hom_inv_id, comp_id] }
  exact ⟨ψ, by ext <;> simp [ψ], by ext <;> simp [ψ]⟩

/-- The image `Φ X = (Φ D, Φ E, Φ α, Φ f, Φ g)` of an exact couple under an exact functor
(`lem-sp-exact-functor-couple`, part 1). -/
@[simps]
noncomputable def mapExact (X : ExactCouple C s) : ExactCouple D s where
  D p q := Φ.obj (X.D p q)
  E p q := Φ.obj (X.E p q)
  α p q p' q' hp hq := Φ.map (X.α p q p' q' hp hq)
  f p q p' q' hp hq := Φ.map (X.f p q p' q' hp hq)
  g p q p' q' hp hq := Φ.map (X.g p q p' q' hp hq)
  f_α a b p q p' q' hp hq hp' hq' := by
    rw [← Φ.map_comp, X.f_α a b p q p' q' hp hq hp' hq', Φ.map_zero]
  g_f a b p q p' q' hp hq hp' hq' := by
    rw [← Φ.map_comp, X.g_f a b p q p' q' hp hq hp' hq', Φ.map_zero]
  α_g a b p q p' q' hp hq hp' hq' := by
    rw [← Φ.map_comp, X.α_g a b p q p' q' hp hq hp' hq', Φ.map_zero]
  exact_f_α a b p q p' q' hp hq hp' hq' := (X.exact_f_α a b p q p' q' hp hq hp' hq').map Φ
  exact_g_f a b p q p' q' hp hq hp' hq' := (X.exact_g_f a b p q p' q' hp hq hp' hq').map Φ
  exact_α_g a b p q p' q' hp hq hp' hq' := (X.exact_α_g a b p q p' q' hp hq hp' hq').map Φ

variable (X : ExactCouple C s)

lemma mapExact_d (p q p' q' : ℤ) (hp : p + s + 2 = p') (hq : q' + s + 1 = q) :
    (X.mapExact Φ).d p q p' q' hp hq = Φ.map (X.d p q p' q' hp hq) := by
  simp [d]

/-- The short complex of differentials of `Φ X` is the image under `Φ` of that of `X`. -/
noncomputable def dScMapIso (p q : ℤ) : (X.dSc p q).map Φ ≅ (X.mapExact Φ).dSc p q :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [mapExact_d]) (by simp [mapExact_d])

/-- The comparison of cycles `Φ (ker d) ⟶ ker (Φ d)`. -/
noncomputable def mapExactCycles (p q : ℤ) :
    Φ.obj (X.dSc p q).cycles ⟶ ((X.mapExact Φ).dSc p q).cycles :=
  ((X.dSc p q).mapCyclesIso Φ).inv ≫ ShortComplex.cyclesMap (X.dScMapIso Φ p q).hom

@[reassoc (attr := simp)]
lemma mapExactCycles_iCycles (p q : ℤ) :
    X.mapExactCycles Φ p q ≫ ((X.mapExact Φ).dSc p q).iCycles = Φ.map (X.dSc p q).iCycles := by
  have h := (X.dSc p q).mapCyclesIso_hom_iCycles Φ
  rw [← Iso.eq_inv_comp] at h
  rw [mapExactCycles, assoc, ShortComplex.cyclesMap_i, h]
  simp [dScMapIso]

/-- The comparison `θ : Φ (ker d / im d) ≅ ker Φd / im Φd` of the `E`-terms of the derived
couples. -/
noncomputable def mapExactE'Iso (p q : ℤ) : Φ.obj (X.E' p q) ≅ (X.mapExact Φ).E' p q :=
  ((X.dSc p q).mapHomologyIso Φ).symm ≪≫ ShortComplex.homologyMapIso (X.dScMapIso Φ p q)

@[reassoc]
lemma map_homologyπ_mapExactE'Iso_hom (p q : ℤ) :
    Φ.map (X.dSc p q).homologyπ ≫ (X.mapExactE'Iso Φ p q).hom =
      X.mapExactCycles Φ p q ≫ ((X.mapExact Φ).dSc p q).homologyπ := by
  have h := ShortComplex.homologyπ_mapHomologyIso_hom Φ (X.dSc p q)
  have h' : Φ.map (X.dSc p q).homologyπ = ((X.dSc p q).mapCyclesIso Φ).inv ≫
      (((X.dSc p q).map Φ).homologyπ ≫ ((X.dSc p q).mapHomologyIso Φ).hom) :=
    ((Iso.inv_comp_eq _).2 h.symm).symm
  rw [h']
  simp [mapExactE'Iso, mapExactCycles, ShortComplex.homologyπ_naturality]

@[reassoc]
lemma kernelComparison_ι' (p q : ℤ) :
    kernelComparison (X.g p q (p + s) (q - s)) Φ ≫ (X.mapExact Φ).ι' p q = Φ.map (X.ι' p q) :=
  kernelComparison_comp_ι _ _

@[reassoc]
lemma map_αbar_kernelComparison (a b p q : ℤ) (ha : p + 1 = a) (hb : b + 1 = q) :
    Φ.map (X.αbar a b p q ha hb) ≫ kernelComparison (X.g p q (p + s) (q - s)) Φ =
      (X.mapExact Φ).αbar a b p q ha hb := by
  rw [← cancel_mono ((X.mapExact Φ).ι' p q), assoc, kernelComparison_ι', ← Φ.map_comp,
    X.αbar_ι' a b p q ha hb, (X.mapExact Φ).αbar_ι' a b p q ha hb, mapExact_α]

@[reassoc]
lemma map_gCycles_mapExactCycles (a b p q : ℤ) (hp : a + s = p) (hq : q + s = b) :
    Φ.map (X.gCycles a b p q hp hq) ≫ X.mapExactCycles Φ p q =
      (X.mapExact Φ).gCycles a b p q hp hq := by
  rw [← cancel_mono ((X.mapExact Φ).dSc p q).iCycles, assoc, mapExactCycles_iCycles,
    ← Φ.map_comp, X.gCycles_i a b p q hp hq, (X.mapExact Φ).gCycles_i a b p q hp hq, mapExact_g]

/-- The comparison morphism `Φ (X') ⟶ (Φ X)'` of exact couples (`lem-sp-exact-functor-couple`,
Step 2): `Φ (ker g) ⟶ ker (Φ g)` on `D`-terms and `θ` on `E`-terms. -/
@[simps]
noncomputable def mapExactDerivedHom : X.derived.mapExact Φ ⟶ (X.mapExact Φ).derived where
  hD p q := kernelComparison (X.g p q (p + s) (q - s)) Φ
  hE p q := (X.mapExactE'Iso Φ p q).hom
  comm_α p q p' q' hp hq := by
    change Φ.map (X.α' p q p' q' hp hq) ≫ kernelComparison (X.g p' q' (p' + s) (q' - s)) Φ =
      kernelComparison (X.g p q (p + s) (q - s)) Φ ≫ (X.mapExact Φ).α' p q p' q' hp hq
    rw [← cancel_mono ((X.mapExact Φ).ι' p' q'), assoc, assoc, kernelComparison_ι',
      (X.mapExact Φ).α'_ι' p q p' q' hp hq, kernelComparison_ι'_assoc, ← Φ.map_comp,
      X.α'_ι' p q p' q' hp hq, Φ.map_comp, mapExact_α]
  comm_f p q p' q' hp hq := by
    change Φ.map (X.f' p q p' q' hp hq) ≫ kernelComparison (X.g p' q' (p' + s) (q' - s)) Φ =
      (X.mapExactE'Iso Φ p q).hom ≫ (X.mapExact Φ).f' p q p' q' hp hq
    rw [← cancel_mono ((X.mapExact Φ).ι' p' q'), ← cancel_epi (Φ.map (X.dSc p q).homologyπ)]
    simp only [assoc]
    rw [kernelComparison_ι', ← Φ.map_comp, ← Φ.map_comp, X.π_f'_assoc p q p' q' hp hq,
      X.fCycles_ι' p q p' q' hp hq, Φ.map_comp, map_homologyπ_mapExactE'Iso_hom_assoc,
      (X.mapExact Φ).π_f'_assoc p q p' q' hp hq, (X.mapExact Φ).fCycles_ι' p q p' q' hp hq,
      mapExact_f, mapExactCycles_iCycles_assoc]
  comm_g p q p' q' hp hq := by
    change Φ.map (X.g' p q p' q' hp hq) ≫ (X.mapExactE'Iso Φ p' q').hom =
      kernelComparison (X.g p q (p + s) (q - s)) Φ ≫ (X.mapExact Φ).g' p q p' q' hp hq
    have hp' : p + 1 + s = p' := by push_cast at hp; lia
    have hq' : q' + s = q - 1 := by push_cast at hq; lia
    rw [← cancel_epi (Φ.map (X.αbar (p + 1) (q - 1) p q rfl (sub_add_cancel q 1))),
      X.map_αbar_kernelComparison_assoc Φ (p + 1) (q - 1) p q rfl (sub_add_cancel q 1),
      (X.mapExact Φ).αbar_g' (p + 1) (q - 1) p q p' q' rfl (sub_add_cancel q 1) hp hq,
      ← Φ.map_comp_assoc, X.αbar_g' (p + 1) (q - 1) p q p' q' rfl (sub_add_cancel q 1) hp hq,
      Φ.map_comp_assoc, X.map_homologyπ_mapExactE'Iso_hom Φ p' q',
      X.map_gCycles_mapExactCycles_assoc Φ (p + 1) (q - 1) p' q' hp' hq']

instance (p q : ℤ) : IsIso ((X.mapExactDerivedHom Φ).hD p q) := by
  rw [mapExactDerivedHom_hD]
  infer_instance

instance (p q : ℤ) : IsIso ((X.mapExactDerivedHom Φ).hE p q) := by
  rw [mapExactDerivedHom_hE]
  infer_instance

instance : IsIso (X.mapExactDerivedHom Φ) := Hom.isIso_of_isIso _

/-- The isomorphism of exact couples `Φ (X') ≅ (Φ X)'` (`lem-sp-exact-functor-couple`, Step 2):
one derived step commutes with `Φ`. -/
noncomputable def mapExactDerivedIso : X.derived.mapExact Φ ≅ (X.mapExact Φ).derived :=
  asIso (X.mapExactDerivedHom Φ)

end

section Iter

variable (X : ExactCouple C 0)

/-- The isomorphisms `(Φ X)_r ≅ Φ (X_r)` of the iterated couples, i.e. of all the pages of
the spectral sequences together with their `D`-terms (`lem-sp-exact-functor-couple`, part 2).
In the notation of the blueprint, the inverse of the component on `E`-terms is `φ_r`. -/
noncomputable def mapExactIterIso : (k : ℕ) → (X.mapExact Φ).iter k ≅ (X.iter k).mapExact Φ
  | 0 => Iso.refl _
  | k + 1 => derivedFunctor.mapIso (mapExactIterIso k) ≪≫ ((X.iter k).mapExactDerivedIso Φ).symm

lemma mapExactIterIso_succ (k : ℕ) :
    X.mapExactIterIso Φ (k + 1) =
      derivedFunctor.mapIso (X.mapExactIterIso Φ k) ≪≫ ((X.iter k).mapExactDerivedIso Φ).symm :=
  rfl

/-- Under the isomorphism `(Φ X)_r ≅ Φ (X_r)`, the `D`-terms `(Φ D)_r` and `Φ (D_r)` are the same
subobject of `Φ D` (`lem-sp-exact-functor-couple`, part 2). -/
@[reassoc]
lemma mapExactIterIso_hom_hD_map_ιIter (k : ℕ) (p q : ℤ) :
    (X.mapExactIterIso Φ k).hom.hD p q ≫ Φ.map (X.ιIter k p q) =
      (X.mapExact Φ).ιIter k p q := by
  induction k with
  | zero => simp [mapExactIterIso]
  | succ k ih =>
    have h : ((X.iter k).mapExactDerivedIso Φ).inv.hD p q ≫ Φ.map ((X.iter k).ι' p q) =
        ((X.iter k).mapExact Φ).ι' p q := by
      rw [← cancel_epi (((X.iter k).mapExactDerivedIso Φ).hom.hD p q), ← comp_hD_assoc,
        Iso.hom_inv_id, id_hD, id_comp]
      exact ((X.iter k).kernelComparison_ι' Φ p q).symm
    rw [mapExactIterIso_succ, Iso.trans_hom, comp_hD, Functor.mapIso_hom, derivedFunctor_map,
      Iso.symm_hom, ιIter_succ, ιIter_succ, Φ.map_comp, Hom.derived_hD, assoc, reassoc_of% h,
      Hom.hD'_ι'_assoc, ih]

/-- The inverse `φ_r` of the isomorphism of `E`-terms commutes with the differentials
(`lem-sp-exact-functor-couple`, part 2). -/
@[reassoc]
lemma mapExactIterIso_inv_comm_d (k : ℕ) (p q p' q' : ℤ) (hp : p + k + 2 = p')
    (hq : q' + k + 1 = q) :
    Φ.map ((X.iter k).d p q p' q' hp hq) ≫ (X.mapExactIterIso Φ k).inv.hE p' q' =
      (X.mapExactIterIso Φ k).inv.hE p q ≫ ((X.mapExact Φ).iter k).d p q p' q' hp hq := by
  rw [← (X.iter k).mapExact_d Φ]
  exact (X.mapExactIterIso Φ k).inv.comm_d p q p' q'

end Iter

section HalfPlane

variable {X : ExactCouple C 0} {a : ℤ}

/-- An exact functor preserves the half-plane hypotheses (`lem-sp-exact-functor-couple`,
part 3). -/
lemma IsHalfPlane.mapExact (h : X.IsHalfPlane a) : (X.mapExact Φ).IsHalfPlane a where
  isZero_D p q hq := Φ.map_isZero (h.isZero_D p q hq)
  isZero_E p q hpq := Φ.map_isZero (h.isZero_E p q hpq)

lemma mapExact_αPow {s : ℕ} (X : ExactCouple C s) (k : ℕ) (a b p q : ℤ) (ha : p + k = a)
    (hb : b + k = q) : (X.mapExact Φ).αPow k a b p q ha hb = Φ.map (X.αPow k a b p q ha hb) := by
  induction k generalizing a b with
  | zero =>
    obtain rfl : a = p := by lia
    obtain rfl : b = q := by lia
    simp [αPow_zero']
  | succ k ih =>
    rw [αPow_succ, αPow_succ, ih, Φ.map_comp, mapExact_α]

variable (X)

/-- The filtration of the abutment `Φ Aⁿ` of `Φ X` is the image under `Φ` of the filtration of
the abutment `Aⁿ` of `X`: `Fᵖ Φ Aⁿ = Φ (Fᵖ Aⁿ)` (`lem-sp-exact-functor-couple`, part 3). -/
lemma mapExact_abutmentFiltration_F (n p : ℤ) :
    ((X.mapExact Φ).abutmentFiltration n).F p =
      imageSubobject (Φ.map ((X.abutmentFiltration n).F p).arrow) := by
  by_cases hp : 0 ≤ p
  · rw [(X.mapExact Φ).abutmentFiltration_F_of_nonneg n p hp p.toNat (by lia),
      Φ.imageSubobject_map_arrow_congr (X.abutmentFiltration_F_of_nonneg n p hp p.toNat (by lia)),
      Φ.imageSubobject_map_arrow, mapExact_αPow]
  · rw [(X.mapExact Φ).abutmentFiltration_F_of_nonpos n p (by lia),
      Φ.imageSubobject_map_arrow_congr (X.abutmentFiltration_F_of_nonpos n p (by lia)),
      imageSubobject_mono, Subobject.mk_eq_top_of_isIso]

/-- The isomorphism `Φ (Fᵖ Aⁿ) ≅ Fᵖ Φ Aⁿ` compatible with the inclusions into `Φ Aⁿ`. -/
noncomputable def mapExactAbutmentStepIso (n p : ℤ) :
    Φ.obj ((X.abutmentFiltration n).F p : C) ≅ (((X.mapExact Φ).abutmentFiltration n).F p : D) :=
  Subobject.isoOfMkEq (Φ.map ((X.abutmentFiltration n).F p).arrow) _
    (by rw [mapExact_abutmentFiltration_F, imageSubobject_mono])

@[reassoc (attr := simp)]
lemma mapExactAbutmentStepIso_hom_arrow (n p : ℤ) :
    (X.mapExactAbutmentStepIso Φ n p).hom ≫ (((X.mapExact Φ).abutmentFiltration n).F p).arrow =
      Φ.map ((X.abutmentFiltration n).F p).arrow := by
  simp [mapExactAbutmentStepIso]

@[reassoc]
lemma map_incl_mapExactAbutmentStepIso_hom (n p : ℤ) :
    Φ.map ((X.abutmentFiltration n).incl p (p + 1)) ≫ (X.mapExactAbutmentStepIso Φ n p).hom =
      (X.mapExactAbutmentStepIso Φ n (p + 1)).hom ≫
        ((X.mapExact Φ).abutmentFiltration n).incl p (p + 1) := by
  rw [← cancel_mono (((X.mapExact Φ).abutmentFiltration n).F p).arrow, assoc, assoc,
    mapExactAbutmentStepIso_hom_arrow, DecreasingFiltration.incl, DecreasingFiltration.incl,
    Subobject.ofLE_arrow, mapExactAbutmentStepIso_hom_arrow, ← Φ.map_comp, Subobject.ofLE_arrow]

/-- The isomorphism `κ : Φ (grᵖ Aⁿ) ≅ grᵖ Φ Aⁿ` (`lem-sp-exact-functor-couple`, part 3). -/
noncomputable def mapExactGrIso (n p : ℤ) :
    Φ.obj ((X.abutmentFiltration n).gr p) ≅ ((X.mapExact Φ).abutmentFiltration n).gr p :=
  PreservesCokernel.iso Φ _ ≪≫
    cokernel.mapIso _ _ (X.mapExactAbutmentStepIso Φ n (p + 1))
      (X.mapExactAbutmentStepIso Φ n p) (X.map_incl_mapExactAbutmentStepIso_hom Φ n p)

@[reassoc]
lemma map_grπ_mapExactGrIso_hom (n p : ℤ) :
    Φ.map ((X.abutmentFiltration n).grπ p) ≫ (X.mapExactGrIso Φ n p).hom =
      (X.mapExactAbutmentStepIso Φ n p).hom ≫ ((X.mapExact Φ).abutmentFiltration n).grπ p := by
  simp [mapExactGrIso, DecreasingFiltration.grπ, DecreasingFiltration.gr]

@[reassoc]
lemma map_abutmentStepToIter_mapExactIterIso_inv (n j : ℤ) (k : ℕ) (u v : ℤ) (hj : 0 ≤ j)
    (hu : u + k = j) (hv : n - j + k = v) (hu0 : u ≤ 0) :
    Φ.map (X.abutmentStepToIter n j k u v hj hu hv hu0) ≫ (X.mapExactIterIso Φ k).inv.hD u v =
      (X.mapExactAbutmentStepIso Φ n j).hom ≫
        (X.mapExact Φ).abutmentStepToIter n j k u v hj hu hv hu0 := by
  have h : (X.mapExactIterIso Φ k).inv.hD u v ≫ (X.mapExact Φ).ιIter k u v =
      Φ.map (X.ιIter k u v) := by
    rw [← X.mapExactIterIso_hom_hD_map_ιIter Φ k u v, ← comp_hD_assoc, Iso.inv_hom_id,
      id_hD, id_comp]
  rw [← cancel_mono ((X.mapExact Φ).ιIter k u v), assoc, assoc, h, ← Φ.map_comp,
    abutmentStepToIter_ιIter, abutmentStepToIter_ιIter, mapExactAbutmentStepIso_hom_arrow_assoc,
    mapExact_αPow, Φ.map_comp]

namespace IsHalfPlane

variable {X} (h : X.IsHalfPlane a)

/-- The isomorphisms `ψ_r : grᵖ A^{p+q} ≅ E_r^{p,q}` of `thm-sp-half-plane-convergence` are
carried by `Φ` to those of `Φ X`: `φ_r ∘ Φ(ψ_r) = ψ_r^Φ ∘ κ`, where
`φ_r = (X.mapExactIterIso Φ k).inv.hE p q : Φ (E_r^{p,q}) ≅ (Φ E)_r^{p,q}`
(`lem-sp-exact-functor-couple`, part 3). -/
lemma mapExact_grIsoIterE (k : ℕ) (p q n : ℤ) (hn : p + q = n) (hp : 0 ≤ p)
    (hk : p + 1 ≤ k) (hk' : q - a ≤ k) :
    Φ.map (h.grIsoIterE k p q n hn hp hk hk').hom ≫ (X.mapExactIterIso Φ k).inv.hE p q =
      (X.mapExactGrIso Φ n p).hom ≫ ((h.mapExact Φ).grIsoIterE k p q n hn hp hk hk').hom := by
  rw [← cancel_epi (Φ.map ((X.abutmentFiltration n).grπ p)), ← Φ.map_comp_assoc,
    grπ_grIsoIterE_hom, map_grπ_mapExactGrIso_hom_assoc, grπ_grIsoIterE_hom, Φ.map_comp_assoc]
  rw [show Φ.map ((X.iter k).g (p - k) (q + k) p q) =
    ((X.iter k).mapExact Φ).g (p - k) (q + k) p q from rfl,
    (X.mapExactIterIso Φ k).inv.comm_g (p - k) (q + k) p q,
    map_abutmentStepToIter_mapExactIterIso_inv_assoc]

end IsHalfPlane

/-- The isomorphism `φ_∞ : Φ (E_∞^{p,q}) ≅ (Φ E)_∞^{p,q}` (`lem-sp-exact-functor-couple`,
part 3): the component of `φ_r` at the page `r` at which `E_∞` is read off. -/
noncomputable def mapExactEInftyIso (p q : ℤ) :
    Φ.obj (X.EInfty a p q) ≅ (X.mapExact Φ).EInfty a p q :=
  ((evalE p q).mapIso (X.mapExactIterIso Φ (stableIndex a p q))).symm

end HalfPlane

end ExactCouple

end CategoryTheory
