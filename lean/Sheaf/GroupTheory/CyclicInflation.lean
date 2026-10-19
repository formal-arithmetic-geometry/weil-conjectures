/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q22
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.Algebra.Ring.ULift
import Sheaf.RepresentationTheory.ResolutionInflationComparison
import Mathlib.GroupTheory.Coset.Basic

/-!
# Inflation between finite cyclic groups

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-lem-base-field-cd/sk-lem-base-field-cd-inflation.proof.md and the inflation paragraph of
sk-lem-base-field-cd/sk-lem-base-field-cd.proof.md (blueprint: det-base-field-cd-inflation).

The two periodic complexes have norm differentials `N_m` and `r N_m`, respectively.
Inflation is induced by the cochain map whose degree `s` component is multiplication
by `r ^ (s / 2)`. Their cohomology groups need not be isomorphic.
-/

@[expose] public section

universe u

open CategoryTheory Rep.FiniteCyclicGroup

namespace groupCohomology

private theorem quotient_sum
    {G H : Type u} [Group G] [Group H] [Fintype G] [Fintype H]
    (π : H →* G) (hπ : Function.Surjective π)
    {A : Type*} [AddCommMonoid A] (a : G → A) :
    ∑ x : H, a (π x) = Nat.card π.ker • ∑ y : G, a y := by
  classical
  rw [← Fintype.sum_fiberwise' π]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro y _
  have hc : Fintype.card {x : H // π x = y} = Nat.card π.ker := by
    change Fintype.card (π ⁻¹' ({y} : Set G)) = Nat.card π.ker
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective hπ y)
  rw [← hc]
  simp

private theorem quotient_kernel_card
    {G H : Type u} [Group G] [Group H] [Fintype G] [Fintype H]
    (m r : ℕ) (hm : 0 < m)
    (hG : Fintype.card G = m) (hH : Fintype.card H = r * m)
    (π : H →* G) (hπ : Function.Surjective π) : Nat.card π.ker = r := by
  have hc := quotient_sum π hπ (fun _ ↦ (1 : ℕ))
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one, hG, hH] at hc
  exact Nat.eq_of_mul_eq_mul_right hm (hc.symm)

private noncomputable def quotientRegular
    {G H : Type u} [Group G] [Group H] (π : H →* G) :
    Rep.leftRegular (ULift.{u} ℤ) H ⟶ Rep.res π (Rep.leftRegular (ULift.{u} ℤ) G) :=
  Rep.leftRegularHom _ (MonoidAlgebra.single 1 1)

set_option backward.isDefEq.respectTransparency false in
private theorem quotientRegular_norm
    {G H : Type u} [CommGroup G] [CommGroup H] [Fintype G] [Fintype H]
    (m r : ℕ) (hm : 0 < m)
    (hG : Fintype.card G = m) (hH : Fintype.card H = r * m)
    (π : H →* G) (hπ : Function.Surjective π) :
    (Rep.leftRegular (ULift.{u} ℤ) H).norm ≫ quotientRegular π =
      r • (quotientRegular π ≫
        (Rep.resFunctor π).map (Rep.leftRegular (ULift.{u} ℤ) G).norm) := by
  apply (Rep.leftRegularHomEquiv _).injective
  change (quotientRegular π).hom
      ((Rep.leftRegular (ULift.{u} ℤ) H).norm.hom (MonoidAlgebra.single 1 1)) =
    r • ((Rep.leftRegular (ULift.{u} ℤ) G).norm.hom
      ((quotientRegular π).hom (MonoidAlgebra.single 1 1)))
  simp only [Rep.norm, Rep.hom_ofHom, Representation.norm, LinearMap.sum_apply,
    Representation.IntertwiningMap.coe_mk, map_sum, Representation.ofMulAction_single,
    smul_eq_mul, mul_one]
  have hsum := quotient_sum π hπ
    (fun y : G ↦ MonoidAlgebra.single y (1 : ULift.{u} ℤ))
  rw [quotient_kernel_card m r hm hG hH π hπ] at hsum
  simpa [quotientRegular] using hsum

set_option backward.isDefEq.respectTransparency false in
private theorem quotientRegular_sub
    {G H : Type u} [CommGroup G] [CommGroup H]
    (g : G) (h : H) (π : H →* G) (hπ : π h = g) :
    (Rep.applyAsHom (Rep.leftRegular (ULift.{u} ℤ) H) h - 𝟙 _) ≫ quotientRegular π =
      quotientRegular π ≫ (Rep.resFunctor π).map
        (Rep.applyAsHom (Rep.leftRegular (ULift.{u} ℤ) G) g - 𝟙 _) := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro x
  simpa [Rep.sub_hom, Rep.applyAsHom, Rep.resMap, hπ] using
    congrArg (fun y ↦ y - (quotientRegular π).hom x)
      (Rep.hom_comm_apply (quotientRegular π) h x)

private theorem homologyMap_zero_of_f_zero
    {K L : CochainComplex (ModuleCat (ULift.{u} ℤ)) ℕ} (F : K ⟶ L)
    (s : ℕ) (hF : F.f s = 0) : HomologicalComplex.homologyMap F s = 0 := by
  have hc : HomologicalComplex.cyclesMap F s = 0 := by
    apply (cancel_mono (L.iCycles s)).mp
    simp [HomologicalComplex.cyclesMap_i, hF]
  apply (cancel_epi (K.homologyπ s)).mp
  simp [HomologicalComplex.homologyπ_naturality, hc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Inflation from a cyclic group of order `m` to one of order `r * m` is computed on
periodic cochains by multiplication by `r ^ (s / 2)` in degree `s`. If `r` kills the
coefficient module, inflation vanishes in every degree at least two. The coefficient
ring `ULift ℤ` allows modules in an arbitrary universe without changing integer modules.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-lem-base-field-cd/sk-lem-base-field-cd-inflation.proof.md and the inflation paragraph of
sk-lem-base-field-cd/sk-lem-base-field-cd.proof.md (blueprint: det-base-field-cd-inflation).

Proof: use the periodic free resolution (lem-sfb-cyclic-periodic-resolution), with maps
alternating between the generator
minus one and the norm. Its exactness follows because the kernel of the augmentation,
and the kernel of the norm, consist of coefficient-sum-zero elements, the image of the
generator minus one; the kernel of the latter is generated by the norm. The quotient
sends the larger generator minus one to the smaller one, and its norm to `r` times the
smaller norm. Thus `r ^ (s / 2)` times the quotient in degree `s` is a chain map lifting
the identity on the trivial integer module: consecutive coefficients agree across odd
boundaries and differ by `r` across even boundaries. Two such lifts are homotopic by
recursive projective lifting into the exact target resolution
(lem-sfb-resolution-inflation-comparison), so this lift computes
inflation as defined using bar cochains. Applying `Hom(-, M)` gives the specified
cochain map and the commuting square under Mathlib's periodic-resolution comparisons.
Finally `s ≥ 2` implies `s / 2 ≥ 1`, so its degree `s` component is zero if `r M = 0`;
the induced cohomology morphism is therefore zero. -/
theorem inflation_periodic
    {G H : Type u} [CommGroup G] [CommGroup H] [Fintype G] [Fintype H]
    (m r : ℕ) (hm : 0 < m) (hr : 0 < r)
    (hG : Fintype.card G = m) (hH : Fintype.card H = r * m)
    (g : G) (h : H) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hh : ∀ x : H, x ∈ Subgroup.zpowers h)
    (π : H →* G) (hπ : π h = g) (M : Rep.{u} (ULift.{u} ℤ) G) :
    (∃ F : moduleCatCochainComplex M g ⟶ moduleCatCochainComplex (Rep.res π M) h,
      (∀ s : ℕ, HEq (F.f s) ((r ^ (s / 2)) • 𝟙 (ModuleCat.of (ULift.{u} ℤ) M.V))) ∧
      (∀ s : ℕ,
        groupCohomology.map π (𝟙 (Rep.res π M)) s ≫
            (groupCohomologyIso (Rep.res π M) s (resolution (ULift.{u} ℤ) h hh) ≪≫
              HomologicalComplex.homologyMapIso (homResolutionIso (Rep.res π M) h hh) s).hom =
          (groupCohomologyIso M s (resolution (ULift.{u} ℤ) g hg) ≪≫
              HomologicalComplex.homologyMapIso (homResolutionIso M g hg) s).hom ≫
            HomologicalComplex.homologyMap F s)) ∧
    ((∀ x : M.V, r • x = 0) →
      ∀ s : ℕ, 2 ≤ s → groupCohomology.map π (𝟙 (Rep.res π M)) s = 0) := by
  have _ := hr
  have hsurj : Function.Surjective π := by
    intro x
    rcases Subgroup.mem_zpowers_iff.mp (hg x) with ⟨n, rfl⟩
    exact ⟨h ^ n, by simp [hπ]⟩
  let f : (resolution (ULift.{u} ℤ) h hh).complex ⟶
      ((Rep.resFunctor (k := ULift.{u} ℤ) π).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (resolution (ULift.{u} ℤ) g hg).complex :=
    { f := fun s ↦ (r ^ (s / 2)) • quotientRegular π
      comm' := by
        rintro i j ⟨rfl⟩
        dsimp [resolution, chainComplexFunctor]
        by_cases hj : Even (j + 1)
        · simp only [hj, ↓reduceIte]
          rw [CategoryTheory.Preadditive.comp_nsmul, quotientRegular_norm m r hm hG hH π hsurj]
          simp only [CategoryTheory.Preadditive.nsmul_comp, smul_smul]
          have he : r ^ ((j + 1) / 2) = r ^ (j / 2) * r := by
            have hj' : (j + 1) / 2 = j / 2 + 1 := by
              rcases hj with ⟨k, hk⟩
              omega
            rw [hj', pow_succ]
          rw [he]
        · simp only [hj, ↓reduceIte]
          rw [CategoryTheory.Preadditive.comp_nsmul, quotientRegular_sub g h π hπ]
          simp only [CategoryTheory.Preadditive.nsmul_comp]
          congr 1
          congr 1
          have hj' : (j + 1) / 2 = j / 2 := by
            have ho : Odd (j + 1) := Nat.not_even_iff_odd.1 hj
            rcases ho with ⟨k, hk⟩
            omega
          rw [hj'] }
  have hf : f.f 0 ≫ (Rep.resFunctor π).map
      ((resolution (ULift.{u} ℤ) g hg).π.f 0) =
        (resolution (ULift.{u} ℤ) h hh).π.f 0 := by
    apply (Rep.leftRegularHomEquiv _).injective
    simp [f, resolution, resolution.π, ChainComplex.toSingle₀Equiv, Rep.homEquiv,
      Rep.resMap, quotientRegular]
  obtain ⟨Fbar, hFbar, hcompare⟩ := resolution_inflation_comparison π hsurj M
    (resolution (ULift.{u} ℤ) g hg) (resolution (ULift.{u} ℤ) h hh) f hf
  let F := (homResolutionIso M g hg).inv ≫ Fbar ≫
    (homResolutionIso (Rep.res π M) h hh).hom
  have hcomponent_eq (s : ℕ) : F.f s =
      ((r ^ (s / 2)) • 𝟙 ((moduleCatCochainComplex M g).X s)) := by
    let : Module (ULift.{u} ℤ) M.V := M.hV2
    ext x
    change M.V at x
    change (Fbar.f s ((Rep.leftRegularHomEquiv M).symm x)).hom
      (MonoidAlgebra.single 1 1) = _
    rw [hFbar]
    simp [f, Rep.nsmul_hom, quotientRegular, Rep.resMap, Rep.homEquiv,
      Finsupp.sum, -Nat.cast_pow]
  have hcomponent (s : ℕ) : HEq (F.f s)
      ((r ^ (s / 2)) • 𝟙 (ModuleCat.of (ULift.{u} ℤ) M.V)) := by
    have hmodule : M.hV2 = (ULift.module : Module (ULift.{u} ℤ) M.V) := by
      apply Module.ext'
      rintro ⟨n⟩ x
      exact @Int.cast_smul_eq_zsmul (ULift.{u} ℤ) M.V _ M.hV1 M.hV2 n x
    have hobj : (moduleCatCochainComplex M g).X s =
        ModuleCat.of (ULift.{u} ℤ) M.V := by
      exact congrArg (fun P : Module (ULift.{u} ℤ) M.V ↦
        @ModuleCat.of (ULift.{u} ℤ) _ M.V M.hV1 P) hmodule
    have hid (X Y : ModuleCat.{u} (ULift.{u} ℤ)) (hXY : X = Y) :
        HEq ((r ^ (s / 2)) • 𝟙 X) ((r ^ (s / 2)) • 𝟙 Y) := by
      cases hXY
      rfl
    exact (heq_of_eq (hcomponent_eq s)).trans (hid _ _ hobj)
  have hsquare (s : ℕ) :
      groupCohomology.map π (𝟙 (Rep.res π M)) s ≫
          (groupCohomologyIso (Rep.res π M) s (resolution (ULift.{u} ℤ) h hh) ≪≫
            HomologicalComplex.homologyMapIso (homResolutionIso (Rep.res π M) h hh) s).hom =
        (groupCohomologyIso M s (resolution (ULift.{u} ℤ) g hg) ≪≫
            HomologicalComplex.homologyMapIso (homResolutionIso M g hg) s).hom ≫
          HomologicalComplex.homologyMap F s := by
    simp only [F, Iso.trans_hom, HomologicalComplex.homologyMapIso_hom,
      HomologicalComplex.homologyMap_comp, Category.assoc]
    rw [← Category.assoc, ← hcompare s]
    simp [← HomologicalComplex.homologyMap_comp_assoc]
  refine ⟨⟨F, hcomponent, hsquare⟩, ?_⟩
  intro hkill s hs
  have hzero : F.f s = 0 := by
    rw [hcomponent_eq s]
    have hpos : 0 < s / 2 := by omega
    obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [ht, pow_succ]
    change (r ^ t * r) • x = 0
    rw [mul_nsmul]
    exact hkill ((r ^ t) • x)
  have hhom := homologyMap_zero_of_f_zero F s hzero
  have he := hsquare s
  rw [hhom, Limits.comp_zero] at he
  apply (cancel_mono
    (groupCohomologyIso (Rep.res π M) s (resolution (ULift.{u} ℤ) h hh) ≪≫
      HomologicalComplex.homologyMapIso (homResolutionIso (Rep.res π M) h hh) s).hom).mp
  simpa using he

end groupCohomology
