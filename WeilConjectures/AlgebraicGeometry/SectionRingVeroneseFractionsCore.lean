/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.InvertibleSectionRing
public import WeilConjectures.AlgebraicGeometry.SectionFractionPresentation
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

@[expose] public section

universe u

open CategoryTheory MonoidalCategory
namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

-- Tensor powers of a section over an open, without extending it globally.
private noncomputable def localPow {M : X.Modules} {U : X.Opens} (e : Γ(M, U)) :
    (n : ℕ) → Γ(M.tensorPow n, U)
  | 0 => unitSectionsEquiv U 1
  | n + 1 => tmulSection e (localPow e n)

private theorem localPow_transport {M : X.Modules} {U : X.Opens} (e : Γ(M, U)) {m n : ℕ}
    (h : m = n) :
    (eqToHom (congrArg M.tensorPow h)).app U (localPow e m) = localPow e n := by
  subst n
  rfl

private theorem isFreeGenerator_localPow {M : X.Modules} {U : X.Opens} {e : Γ(M, U)}
    (he : IsFreeGenerator e) (n : ℕ) : IsFreeGenerator (localPow e n) := by
  induction n with
  | zero => exact isFreeGenerator_one U
  | succ n ih => exact he.tmulSection ih

private theorem tensorPowAddIso_inv_app_localPow {M : X.Modules} {U : X.Opens}
    (e : Γ(M, U)) (i j : ℕ) :
    (M.tensorPowAddIso i j).inv.app U (tmulSection (localPow e i) (localPow e j)) =
      localPow e (i + j) := by
  induction i with
  | zero =>
    exact (congrArg ((eqToHom (congrArg M.tensorPow (Nat.zero_add j).symm)).app U)
      ((leftUnitor_hom_app_tmulSection 1 (localPow e j)).trans (one_smul _ _))).trans
      (localPow_transport e (Nat.zero_add j).symm)
  | succ i ih =>
    have h : (Iso.refl M ⊗ᵢ M.tensorPowAddIso i j).inv.app U
        (tmulSection e (tmulSection (localPow e i) (localPow e j))) =
          tmulSection e (localPow e (i + j)) := by
      rw [tensorIso_inv, Iso.refl_inv, tensorHom_app_tmulSection, ih, Hom.id_app]
      rfl
    exact (congrArg ((eqToHom (congrArg M.tensorPow (Nat.succ_add i j).symm)).app U)
      ((congrArg _ (associator_hom_app_tmulSection _ _ _)).trans h)).trans
      (localPow_transport e (Nat.succ_add i j).symm)

private theorem tensorPowMulIso_inv_app_localPow {M : X.Modules} {U : X.Opens}
    (e : Γ(M, U)) (d n : ℕ) :
    (M.tensorPowMulIso d n).inv.app U (localPow (localPow e d) n) = localPow e (d * n) := by
  induction n with
  | zero => exact localPow_transport e (Nat.mul_zero d).symm
  | succ n ih =>
    have h : (Iso.refl (M.tensorPow d) ⊗ᵢ M.tensorPowMulIso d n).inv.app U
        (localPow (localPow e d) (n + 1)) = tmulSection (localPow e d) (localPow e (d * n)) := by
      rw [tensorIso_inv, Iso.refl_inv]
      exact (tensorHom_app_tmulSection _ _ _ _).trans (congrArg _ ih)
    have hinv : (M.tensorPowMulIso d (n + 1)).inv =
        (Iso.refl (M.tensorPow d) ⊗ᵢ M.tensorPowMulIso d n).inv ≫
          (M.tensorPowAddIso d (d * n)).inv ≫ eqToHom (congrArg M.tensorPow (by ring)) :=
      rfl
    rw [hinv]
    exact (congrArg ((eqToHom (congrArg M.tensorPow (by ring : d + d * n = d * (n + 1)))).app U)
      ((congrArg ((M.tensorPowAddIso d (d * n)).inv.app U) h).trans
        (tensorPowAddIso_inv_app_localPow e d (d * n)))).trans
        (localPow_transport e (by ring))

-- If `s(1) = g • f` on `U`, then `s^{⊗ b}(1) = g ^ b • f^{⊗ b}` on `U`.
private theorem tensorPowSectionOne_eq_smul_localPow {M : X.Modules} {U : X.Opens}
    (s : 𝟙_ X.Modules ⟶ M) {f : Γ(M, U)} {g : Γ(X, U)}
    (hs : s.app U (unitSectionsEquiv U 1) = g • f) (b : ℕ) :
    tensorPowSectionOne s b U = g ^ b • localPow f b := by
  induction b with
  | zero =>
    rw [pow_zero, one_smul]
    rfl
  | succ b ih =>
    rw [tensorPowSectionOne_succ, hs, ih, smul_tmulSection, tmulSection_smul, smul_smul,
      pow_succ']
    rfl

private theorem mulTensorPowSection_app_localPow {M : X.Modules} {U : X.Opens}
    (s : 𝟙_ X.Modules ⟶ M) {f : Γ(M, U)} {g : Γ(X, U)}
    (hs : s.app U (unitSectionsEquiv U 1) = g • f) (F : X.Modules) (a b : ℕ) (x : Γ(F, U)) :
    (mulTensorPowSection s F a b).app U (tmulSection x (localPow f a)) =
      g ^ b • tmulSection x (localPow f (a + b)) := by
  rw [mulTensorPowSection_app, tensorPowSectionOne_eq_smul_localPow s hs, tmulSection_smul,
    Hom.app_smul, Hom.app_smul, associator_hom_app_tmulSection, whiskerLeft_app_tmulSection,
    tensorPowAddIso_inv_app_localPow]

-- Convert the scheme-module trivialization to a trivialization over the restricted site.
private theorem exists_localFreeGenerator (L : X.Modules) [L.IsInvertible] (x : X) :
    ∃ (U : X.Opens), x ∈ U ∧ ∃ e : Γ(L, U), IsFreeGenerator e := by
  obtain ⟨U, hx, ⟨e⟩⟩ := IsInvertible.exists_isoUnit (M := L) x
  let e' := (overEquiv U).functor.preimageIso
    ((overFunctorEquiv U).app L ≪≫ (restrictFunctorIsoPullback U.ι).app L ≪≫ e ≪≫
      overEquivFunctorObjUnitIso U)
  obtain ⟨s, hs⟩ := exists_isFreeGenerator_of_iso e'
  exact ⟨U, hx, s, hs⟩

-- Two global sections agree if they agree on every open on which `L` has a free generator.
private theorem eq_of_restrict_eq_of_isFreeGenerator (L : X.Modules) [L.IsInvertible]
    {N : X.Modules} {x y : Γ(N, ⊤)}
    (h : ∀ (U : X.Opens) (e : Γ(L, U)), IsFreeGenerator e →
      N.presheaf.map (homOfLE le_top : U ⟶ ⊤).op x =
        N.presheaf.map (homOfLE le_top : U ⟶ ⊤).op y) :
    x = y := by
  let S : Sieve (⊤ : X.Opens) := {
    arrows U _ := ∃ e : Γ(L, U), IsFreeGenerator e
    downward_closed := fun ⟨e, he⟩ g ↦ ⟨_, he.map (leOfHom g)⟩ }
  have hS : S ∈ Opens.grothendieckTopology X ⊤ := by
    intro x _
    obtain ⟨U, hx, e, he⟩ := exists_localFreeGenerator L x
    exact ⟨U, homOfLE le_top, ⟨e, he⟩, hx⟩
  refine (N.isSheaf_presheaf_comp_forget _ hS).isSeparatedFor.ext fun U f ⟨e, he⟩ ↦ ?_
  rw [Subsingleton.elim f (homOfLE le_top)]
  exact h U e he

/-- The canonical isomorphism `𝒪_X ⊗ (L^{⊗ d})^{⊗ n} ≅ L^{⊗ n d}`, identifying the numerators
of the fraction presentation with the homogeneous components of the section ring in degrees
divisible by `d` (blueprint: lem-sc-section-ring-veronese-fractions-core). -/
noncomputable def veroneseTensorPowIso (L : X.Modules) (d n : ℕ) :
    𝟙_ X.Modules ⊗ (L.tensorPow d).tensorPow n ≅ L.tensorPow (n * d) :=
  λ_ _ ≪≫ (L.tensorPowMulIso d n).symm ≪≫ eqToIso (congrArg L.tensorPow (Nat.mul_comm d n))

private theorem veroneseTensorPowIso_hom_app_localPow (L : X.Modules) {U : X.Opens}
    (e : Γ(L, U)) (d n : ℕ) (r : Γ(X, U)) :
    (veroneseTensorPowIso L d n).hom.app U
      (tmulSection (unitSectionsEquiv U r) (localPow (localPow e d) n)) =
        r • localPow e (n * d) := by
  have h := congrArg ((eqToHom (congrArg L.tensorPow (Nat.mul_comm d n))).app U)
    (congrArg ((L.tensorPowMulIso d n).inv.app U)
      (leftUnitor_hom_app_tmulSection r (localPow (localPow e d) n)))
  rw [Hom.app_smul, Hom.app_smul, tensorPowMulIso_inv_app_localPow,
    localPow_transport e (Nat.mul_comm d n)] at h
  exact h

private theorem eqToHom_app_heq {M N : X.Modules} {U : X.Opens} (h : M = N)
    (a : Γ(M, U)) : (eqToHom h).app U a ≍ a := by
  subst N
  rfl

-- Restrict the data of a fraction to an open on which `L` has a free generator `e`.
private theorem exists_restrict_eq_smul (L : X.Modules) {d n : ℕ} {U : X.Opens} {e : Γ(L, U)}
    (he : IsFreeGenerator e) (σ : Γ(L.tensorPow d, ⊤))
    (t : Γ(𝟙_ X.Modules ⊗ (L.tensorPow d).tensorPow n, ⊤)) :
    ∃ f g : Γ(X, U),
      f • tmulSection (unitSectionsEquiv U 1) (localPow (localPow e d) n) =
        (𝟙_ X.Modules ⊗ (L.tensorPow d).tensorPow n).presheaf.map
          (homOfLE le_top : U ⟶ ⊤).op t ∧
      (homOfGlobalSection (L.tensorPow d) σ).app U (unitSectionsEquiv U 1) =
        g • localPow e d ∧
      g • localPow e d = (L.tensorPow d).presheaf.map (homOfLE le_top : U ⟶ ⊤).op σ := by
  obtain ⟨f, hf⟩ := ((isFreeGenerator_one U).tmulSection
    (isFreeGenerator_localPow (isFreeGenerator_localPow he d) n)).exists_smul_eq
      ((𝟙_ X.Modules ⊗ (L.tensorPow d).tensorPow n).presheaf.map (homOfLE le_top : U ⟶ ⊤).op t)
  obtain ⟨g, hg⟩ := (isFreeGenerator_localPow he d).exists_smul_eq
    ((L.tensorPow d).presheaf.map (homOfLE le_top : U ⟶ ⊤).op σ)
  exact ⟨f, g, hf, (homOfGlobalSection_app_one _ σ U).trans hg.symm, hg⟩

private theorem mulTensorPowSection_homOfGlobalSection_zero (L : X.Modules) [L.IsInvertible]
    {d : ℕ} (σ : Γ(L.tensorPow d, ⊤)) (n : ℕ)
    (t : Γ(𝟙_ X.Modules ⊗ (L.tensorPow d).tensorPow n, ⊤)) :
    (mulTensorPowSection (homOfGlobalSection _ σ) (𝟙_ X.Modules) n 0).app ⊤ t = t := by
  refine eq_of_restrict_eq_of_isFreeGenerator L fun U e he ↦ ?_
  obtain ⟨f, g, hf, hs, -⟩ := exists_restrict_eq_smul L he σ t
  rw [← Hom.app_presheaf_map, ← hf, Hom.app_smul, mulTensorPowSection_app_localPow _ hs,
    pow_zero, one_smul]
  exact hf

private theorem mulTensorPowSection_homOfGlobalSection_succ (L : X.Modules) [L.IsInvertible]
    {d : ℕ} (σ : Γ(L.tensorPow d, ⊤)) (n b : ℕ)
    (t : Γ(𝟙_ X.Modules ⊗ (L.tensorPow d).tensorPow n, ⊤)) :
    (mulTensorPowSection (homOfGlobalSection _ σ) (𝟙_ X.Modules) n (b + 1)).app ⊤ t =
      (mulTensorPowSection (homOfGlobalSection _ σ) (𝟙_ X.Modules) (n + b) 1).app ⊤
        ((mulTensorPowSection (homOfGlobalSection _ σ) (𝟙_ X.Modules) n b).app ⊤ t) := by
  refine eq_of_restrict_eq_of_isFreeGenerator L fun U e he ↦ ?_
  obtain ⟨f, g, hf, hs, -⟩ := exists_restrict_eq_smul L he σ t
  have h : (𝟙_ X.Modules ⊗ (L.tensorPow d).tensorPow (n + b + 1)).presheaf.map
      (homOfLE le_top : U ⟶ ⊤).op
        ((mulTensorPowSection (homOfGlobalSection _ σ) (𝟙_ X.Modules) (n + b) 1).app ⊤
          ((mulTensorPowSection (homOfGlobalSection _ σ) (𝟙_ X.Modules) n b).app ⊤ t)) =
      (f * g ^ (b + 1)) •
        tmulSection (unitSectionsEquiv U 1) (localPow (localPow e d) (n + b + 1)) := by
    rw [← Hom.app_presheaf_map, ← Hom.app_presheaf_map, ← hf, Hom.app_smul, Hom.app_smul,
      mulTensorPowSection_app_localPow _ hs, Hom.app_smul, mulTensorPowSection_app_localPow _ hs,
      smul_smul, smul_smul, pow_one, pow_succ, mul_assoc]
  rw [← Hom.app_presheaf_map, ← hf, Hom.app_smul, mulTensorPowSection_app_localPow _ hs,
    smul_smul]
  exact h.symm

private theorem veroneseTensorPowIso_mulTensorPowSection_one (L : X.Modules) [L.IsInvertible]
    {d : ℕ} (σ : Γ(L.tensorPow d, ⊤)) (n : ℕ)
    (t : Γ(𝟙_ X.Modules ⊗ (L.tensorPow d).tensorPow n, ⊤)) :
    (veroneseTensorPowIso L d (n + 1)).hom.app ⊤
      ((mulTensorPowSection (homOfGlobalSection _ σ) (𝟙_ X.Modules) n 1).app ⊤ t) =
    (eqToHom (congrArg L.tensorPow (add_one_mul n d).symm)).app ⊤
      ((L.tensorPowAddIso (n * d) d).inv.app ⊤
        (tmulSection ((veroneseTensorPowIso L d n).hom.app ⊤ t) σ)) := by
  refine eq_of_restrict_eq_of_isFreeGenerator L fun U e he ↦ ?_
  obtain ⟨f, g, hf, hs, hg⟩ := exists_restrict_eq_smul L he σ t
  simp only [← Hom.app_presheaf_map, tmulSection_map]
  rw [← hf, ← hg]
  simp only [Hom.app_smul, mulTensorPowSection_app_localPow _ hs,
    veroneseTensorPowIso_hom_app_localPow, smul_tmulSection, tmulSection_smul,
    tensorPowAddIso_inv_app_localPow, smul_smul, pow_one, one_smul]
  rw [localPow_transport e (add_one_mul n d).symm, mul_comm f g]

/-- In the fraction presentation, `[n, t] = [n + b, t ⊗ s^b]`
(blueprint: def-sc-section-fraction-presentation). -/
theorem sectionFraction_eq_sectionFraction_mulTensorPowSection (L F : X.Modules)
    (s : Γ(L, ⊤)) (n b : ℕ) (t : Γ(F ⊗ L.tensorPow n, ⊤)) :
    sectionFraction L F s n t = sectionFraction L F s (n + b)
      ((mulTensorPowSection (homOfGlobalSection L s) F n b).app ⊤ t) :=
  (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨n, b, t, rfl⟩)

/-- Every fraction can be rewritten with any larger denominator exponent. -/
theorem exists_sectionFraction_eq_of_le (L F : X.Modules) (s : Γ(L, ⊤)) {n N : ℕ}
    (h : n ≤ N) (t : Γ(F ⊗ L.tensorPow n, ⊤)) :
    ∃ t' : Γ(F ⊗ L.tensorPow N, ⊤), sectionFraction L F s n t = sectionFraction L F s N t' := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le h
  exact ⟨_, sectionFraction_eq_sectionFraction_mulTensorPowSection L F s n b t⟩

/-- Every element of the fraction presentation is a single fraction `[n, t]`
(blueprint: def-sc-section-fraction-presentation). -/
theorem exists_sectionFraction_eq (L F : X.Modules) (s : Γ(L, ⊤))
    (x : SectionFractionPresentation L F s) :
    ∃ (n : ℕ) (t : Γ(F ⊗ L.tensorPow n, ⊤)), sectionFraction L F s n t = x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  induction z using DirectSum.induction_on with
  | zero => exact ⟨0, 0, by rw [sectionFraction, map_zero, Submodule.Quotient.mk_zero]⟩
  | of n t => exact ⟨n, t, rfl⟩
  | add z w hz hw =>
    obtain ⟨n, t, ht⟩ := hz
    obtain ⟨m, u, hu⟩ := hw
    obtain ⟨t', ht'⟩ := exists_sectionFraction_eq_of_le L F s (Nat.le_add_right n m) t
    obtain ⟨u', hu'⟩ := exists_sectionFraction_eq_of_le L F s (Nat.le_add_left m n) u
    refine ⟨n + m, t' + u', ?_⟩
    rw [Submodule.Quotient.mk_add, ← ht, ← hu, ht', hu', sectionFraction, sectionFraction,
      sectionFraction, map_add, Submodule.Quotient.mk_add]

/-- The numerator `ξ` of the fraction `[n, ξ] = ξ / sⁿ`, as an element of degree `n d` of the
section ring (blueprint: lem-sc-section-ring-veronese-fractions-core). -/
noncomputable def veroneseNumerator (L : X.Modules) (d n : ℕ)
    (t : Γ(𝟙_ X.Modules ⊗ (L.tensorPow d).tensorPow n, ⊤)) : InvertibleSectionRing L :=
  DirectSum.of (SectionRingComponent L) (n * d) ((veroneseTensorPowIso L d n).hom.app ⊤ t)

theorem veroneseNumerator_mem (L : X.Modules) (d n : ℕ)
    (t : Γ(𝟙_ X.Modules ⊗ (L.tensorPow d).tensorPow n, ⊤)) :
    veroneseNumerator L d n t ∈ sectionRingGrade L (n • d) :=
  ⟨_, rfl⟩

theorem veroneseNumerator_add (L : X.Modules) (d n : ℕ)
    (t t' : Γ(𝟙_ X.Modules ⊗ (L.tensorPow d).tensorPow n, ⊤)) :
    veroneseNumerator L d n (t + t') = veroneseNumerator L d n t + veroneseNumerator L d n t' := by
  rw [veroneseNumerator, map_add, map_add, veroneseNumerator, veroneseNumerator]

theorem veroneseNumerator_zero (L : X.Modules) (d n : ℕ) :
    veroneseNumerator L d n 0 = 0 := by
  rw [veroneseNumerator, map_zero, map_zero]

/-- Multiplying the numerator by `s^{⊗ b}` multiplies the element of the section ring by
`s ^ b` (blueprint: lem-sc-section-ring-veronese-fractions-core). -/
theorem veroneseNumerator_mulTensorPowSection (L : X.Modules) [L.IsInvertible] {d : ℕ}
    (σ : Γ(L.tensorPow d, ⊤)) (n b : ℕ)
    (t : Γ(𝟙_ X.Modules ⊗ (L.tensorPow d).tensorPow n, ⊤)) :
    veroneseNumerator L d (n + b)
        ((mulTensorPowSection (homOfGlobalSection _ σ) (𝟙_ X.Modules) n b).app ⊤ t) =
      veroneseNumerator L d n t * DirectSum.of (SectionRingComponent L) d σ ^ b := by
  induction b with
  | zero =>
    rw [pow_zero, mul_one]
    exact congrArg (veroneseNumerator L d n) (mulTensorPowSection_homOfGlobalSection_zero L σ n t)
  | succ b ih =>
    rw [mulTensorPowSection_homOfGlobalSection_succ, pow_succ, ← mul_assoc, ← ih,
      veroneseNumerator, veroneseNumerator, DirectSum.of_mul_of]
    refine DirectSum.of_eq_of_gradedMonoid_eq (Sigma.ext (add_one_mul (n + b) d) ?_)
    exact (heq_of_eq (veroneseTensorPowIso_mulTensorPowSection_one L σ (n + b) _)).trans
      (eqToHom_app_heq _ _)

open HomogeneousLocalization in
/-- The fraction `ξ / sⁿ` in the degree-zero localization of the section ring at `s`
(blueprint: lem-sc-section-ring-veronese-fractions-core). -/
noncomputable def veroneseFraction (L : X.Modules) [L.IsInvertible] {d : ℕ}
    (s : sectionRingGrade L d) (n : ℕ)
    (t : Γ(𝟙_ X.Modules ⊗ (L.tensorPow d).tensorPow n, ⊤)) : Away (sectionRingGrade L) s.val :=
  Away.mk _ s.2 n (veroneseNumerator L d n t) (veroneseNumerator_mem L d n t)

theorem veroneseFraction_val (L : X.Modules) [L.IsInvertible] {d : ℕ}
    (s : sectionRingGrade L d) (n : ℕ)
    (t : Γ(𝟙_ X.Modules ⊗ (L.tensorPow d).tensorPow n, ⊤)) :
    (veroneseFraction L s n t).val =
      Localization.mk (veroneseNumerator L d n t)
        (⟨s.val ^ n, n, rfl⟩ : Submonoid.powers s.val) :=
  HomogeneousLocalization.Away.val_mk _ _ _ _ _

-- A homogeneous element of degree `d` is the single-component family of its degree-`d` entry.
private theorem of_apply_eq (L : X.Modules) {d : ℕ} (s : sectionRingGrade L d) :
    DirectSum.of (SectionRingComponent L) d (s.val d) = s.val := by
  obtain ⟨_, c, rfl⟩ := s
  rw [DirectSum.of_eq_same]

/-- The fraction `ξ / sⁿ` as an additive map in the numerator `ξ`
(blueprint: lem-sc-section-ring-veronese-fractions-core). -/
noncomputable def veroneseFractionHom (L : X.Modules) [L.IsInvertible] {d : ℕ}
    (s : sectionRingGrade L d) (n : ℕ) :
    Γ(𝟙_ X.Modules ⊗ (L.tensorPow d).tensorPow n, ⊤) →+
      HomogeneousLocalization.Away (sectionRingGrade L) s.val where
  toFun := veroneseFraction L s n
  map_zero' := by
    refine HomogeneousLocalization.val_injective _ ?_
    rw [veroneseFraction_val, HomogeneousLocalization.val_zero, veroneseNumerator_zero,
      Localization.mk_zero]
  map_add' t t' := by
    refine HomogeneousLocalization.val_injective _ ?_
    rw [HomogeneousLocalization.val_add, veroneseFraction_val, veroneseFraction_val,
      veroneseFraction_val, Localization.add_mk_self, veroneseNumerator_add]

-- The fraction `ξ / sⁿ` is unchanged by `[n, ξ] = [n + b, ξ ⊗ s^b]`.
private theorem veroneseFraction_mulTensorPowSection (L : X.Modules) [L.IsInvertible] {d : ℕ}
    (s : sectionRingGrade L d) (n b : ℕ)
    (t : Γ(𝟙_ X.Modules ⊗ (L.tensorPow d).tensorPow n, ⊤)) :
    veroneseFraction L s (n + b)
        ((mulTensorPowSection (homOfGlobalSection _ (s.val d)) (𝟙_ X.Modules) n b).app ⊤ t) =
      veroneseFraction L s n t := by
  refine HomogeneousLocalization.val_injective _ ?_
  rw [veroneseFraction_val, veroneseFraction_val, veroneseNumerator_mulTensorPowSection,
    of_apply_eq, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  exact ⟨1, by simp only [pow_add]; ring⟩

/-- The canonical map `[n, ξ] ↦ ξ / sⁿ` from the fraction presentation of the Veronese
fractions to the degree-zero localization of the section ring at `s`
(blueprint: lem-sc-section-ring-veronese-fractions-core). -/
noncomputable def sectionFractionToAway (L : X.Modules) [L.IsInvertible] {d : ℕ}
    (s : sectionRingGrade L d) :
    SectionFractionPresentation (L.tensorPow d) (𝟙_ X.Modules) (s.val d) →+
      HomogeneousLocalization.Away (sectionRingGrade L) s.val :=
  QuotientAddGroup.lift
    (sectionFractionRelations (L.tensorPow d) (𝟙_ X.Modules) (s.val d)).toAddSubgroup
    (DirectSum.toAddMonoid (veroneseFractionHom L s)) <| by
    have key (z) (hz : z ∈ sectionFractionRelations (L.tensorPow d) (𝟙_ X.Modules) (s.val d))
        (r : Γ(X, ⊤)) : DirectSum.toAddMonoid (veroneseFractionHom L s) (r • z) = 0 := by
      induction hz using Submodule.span_induction generalizing r with
      | mem z hz =>
        obtain ⟨n, b, t, rfl⟩ := hz
        rw [smul_sub, ← DirectSum.of_smul, ← DirectSum.of_smul, ← Hom.app_smul, map_sub,
          DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of, sub_eq_zero]
        exact (veroneseFraction_mulTensorPowSection L s n b (r • t)).symm
      | zero => rw [smul_zero, map_zero]
      | add z w _ _ hz hw => rw [smul_add, map_add, hz, hw, add_zero]
      | smul a z _ hz => rw [smul_smul, hz]
    intro z hz
    rw [AddMonoidHom.mem_ker, ← one_smul Γ(X, ⊤) z]
    exact key z hz 1

/-- The canonical map sends `[n, ξ]` to `ξ / sⁿ`. -/
theorem sectionFractionToAway_sectionFraction (L : X.Modules) [L.IsInvertible] {d : ℕ}
    (s : sectionRingGrade L d) (n : ℕ)
    (t : Γ(𝟙_ X.Modules ⊗ (L.tensorPow d).tensorPow n, ⊤)) :
    sectionFractionToAway L s (sectionFraction _ _ _ n t) = veroneseFraction L s n t :=
  (QuotientAddGroup.lift_mk _ _ _).trans (DirectSum.toAddMonoid_of _ _ _)

/-- Core identification for the Veronese fraction presentation: the canonical map
`[n, ξ] ↦ ξ / sⁿ` from the fraction presentation to the degree-zero localization of the section
ring at `s` is bijective.
Source: Stacks Project, Properties, Tag 0B5L and Lemma 01PW(2).
(blueprint: lem-sc-section-ring-veronese-fractions-core)
Every element of the presentation is a single fraction `[n, ξ]`, and every element of the
localization is a single fraction `ξ / sⁿ` with `ξ` homogeneous of degree `n d`; the summand of
degree `n d` is identified with the `n`-th tensor power of `L^{⊗ d}`. A fraction vanishes in the
localization iff `ξ sᵏ = 0` for some `k`, i.e. iff `[n, ξ] = [n + k, ξ ⊗ sᵏ] = 0`.
-/
theorem sectionRing_veronese_fraction_core
    (X : Scheme.{u}) (L : X.Modules) [L.IsInvertible]
    (d : ℕ) (s : sectionRingGrade L d) :
    Function.Bijective (sectionFractionToAway L s) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨n, t, rfl⟩ := exists_sectionFraction_eq _ _ _ x
    rw [sectionFractionToAway_sectionFraction] at hx
    have hval := congrArg HomogeneousLocalization.val hx
    rw [veroneseFraction_val, HomogeneousLocalization.val_zero, Localization.mk_eq_mk',
      IsLocalization.mk'_eq_zero_iff] at hval
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := hval
    have h0 : veroneseNumerator L d (n + k)
        ((mulTensorPowSection (homOfGlobalSection _ (s.val d)) (𝟙_ X.Modules) n k).app ⊤ t) =
          0 := by
      rw [veroneseNumerator_mulTensorPowSection, of_apply_eq,
        mul_comm (veroneseNumerator L d n t)]
      exact hk
    have h1 : (mulTensorPowSection (homOfGlobalSection _ (s.val d)) (𝟙_ X.Modules) n k).app ⊤ t =
        0 := by
      refine (bijective_app_of_iso (veroneseTensorPowIso L d (n + k)) ⊤).1 ?_
      rw [map_zero]
      exact DirectSum.of_injective ((n + k) * d) (h0.trans (map_zero _).symm)
    rw [sectionFraction_eq_sectionFraction_mulTensorPowSection _ _ _ n k, h1, sectionFraction,
      map_zero, Submodule.Quotient.mk_zero]
  · obtain ⟨n, a, ⟨c, rfl⟩, rfl⟩ := HomogeneousLocalization.Away.mk_surjective _ s.2 y
    refine ⟨sectionFraction _ _ _ n ((veroneseTensorPowIso L d n).inv.app ⊤ c), ?_⟩
    have hc := inv_app_hom_app_apply_of_iso (veroneseTensorPowIso L d n).symm c
    rw [Iso.symm_inv, Iso.symm_hom] at hc
    rw [sectionFractionToAway_sectionFraction, veroneseFraction]
    congr 1
    rw [veroneseNumerator, hc]
    rfl

end AlgebraicGeometry.Scheme.Modules
