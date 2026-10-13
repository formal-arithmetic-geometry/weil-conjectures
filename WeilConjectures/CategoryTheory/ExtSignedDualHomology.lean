/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.CategoryTheory.Preadditive.Projective.Resolution

import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Projective.Ext

/-! # Ext and an explicit signed dual of a projective resolution

Source: Stacks Project, Tag 0BQZ, computation by the total Hom complex;
Mathlib's ProjectiveResolution.extAddEquivCohomologyClass and
HomComplex.Cochain.toSingleEquiv implement the two comparison steps.
(blueprint: new-j3-ext-signed-dual-homology).
-/

@[expose] public section

universe u

open CategoryTheory

namespace CategoryTheory.ProjectiveResolution

set_option backward.isDefEq.respectTransparency false in
private theorem extMk_zero_iff
    (A : Type u) [CommRing A] [HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]
    {X Y : ModuleCat.{u} A} (P : ProjectiveResolution X)
    (f : P.complex.X 0 ⟶ Y) (hf : P.complex.d 1 0 ≫ f = 0) :
    P.extMk f 1 rfl hf = 0 ↔ f = 0 := by
  open CochainComplex HomComplex in
    simp only [← P.extEquivCohomologyClass.apply_eq_iff_eq,
      extEquivCohomologyClass_extMk, extEquivCohomologyClass_zero,
      CohomologyClass.mk_eq_zero_iff]
    rw [Cocycle.toSingleMk_mem_coboundaries_iff _ _ _ _ _ 1 (by norm_num)]
    constructor
    · rintro ⟨g, hg⟩
      have hg0 : g = 0 := (P.cochainComplex.isZero_of_isStrictlyLE 0 1).eq_of_src _ _
      rw [hg0, Limits.comp_zero] at hg
      exact (cancel_epi (P.cochainComplexXIso 0 0 rfl).hom).mp (by simpa using hg.symm)
    · rintro rfl
      exact ⟨0, by simp⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.defeqAttrib.useBackward true in
/-- Any cochain complex identified termwise with the signed dual of a projective
resolution computes Ext. Source: Stacks Project, Tag 0BQZ, total Hom computation.
(blueprint: new-j3-ext-signed-dual-homology).

Proof: Apply ProjectiveResolution.extAddEquivCohomologyClass to P and Y.
A degree-n cochain from P.cochainComplex to Y[0] has only the component from
P_n to Y, since all other target terms are zero. Evaluation at that component
is the additive equivalence Cochain.toSingleEquiv, using P.cochainComplexXIso
to identify degree -n with P_n. The formula Cochain.δ_toSingleMk gives
(-1)^(n+1) times precomposition with d_(n+1) as its differential. The displayed
compatibility hd and the component isomorphisms e identify kernels with the
cycles of L and images with its boundaries. Explicitly, send a cocycle to e_n
inverse applied to its evaluated component; conversely, apply e_n to an
L-cycle and use Cochain.toSingleMk to put it in the unique component. The
cocycle condition follows from hd. For n > 0 the same maps in degree n-1
carry a coboundary to the differential of its image, and conversely lift any
L-boundary to that cochain, by hd. Thus the inverse maps descend to the
quotients and remain inverses. The preceding degree for n = 0
is zero because P.cochainComplex has zero terms in positive degrees, matching
L's zero incoming differential. Pass to the kernel/image quotient to obtain
an additive equivalence with L.homology n.
To check A-linearity, represent an Ext class by P.extMk of a cocycle g.
Ext.smul_eq_comp_mk₀ and ProjectiveResolution.extMk_comp_mk₀ show that
multiplication by a is represented by g followed by a times id_Y, which is a*g.
Component evaluation, each e_i, and passage to the quotient commute with this
scalar multiplication. ExtMk surjectivity proves scalar compatibility on every
class, so the additive equivalence is A-linear. This argument uses neither
Koszul regularity nor an exterior basis: those are used only to produce P. -/
theorem exists_ext_signed_dual_homology_equiv
    (A : Type u) [CommRing A] [HasDerivedCategory.{u + 1} (ModuleCat.{u} A)]
    {X Y : ModuleCat.{u} A} (P : ProjectiveResolution X)
    (L : CochainComplex (ModuleCat.{u} A) ℕ)
    (e : ∀ i, L.X i ≅ ModuleCat.of A (P.complex.X i ⟶ Y))
    (hd : ∀ i, L.d i (i + 1) ≫ (e (i + 1)).hom =
      (e i).hom ≫ ModuleCat.ofHom
        ((-1 : A) ^ (i + 1) • Linear.leftComp A Y (P.complex.d (i + 1) i)))
    (n : ℕ) :
    Nonempty (Abelian.Ext X Y n ≃ₗ[A] L.homology n) := by
  classical
  let S := L.sc n
  have hn : (ComplexShape.up ℕ).next n = n + 1 :=
    (ComplexShape.up ℕ).next_eq' (by rfl)
  have hc (x : LinearMap.ker S.g.hom) :
      P.complex.d (n + 1) n ≫ (e n).hom x.val = 0 := by
    have hx : L.d n (n + 1) x.val = 0 := by
      have hx := LinearMap.mem_ker.mp x.property
      change L.d n ((ComplexShape.up ℕ).next n) x.val = 0 at hx
      rwa [hn] at hx
    have h := ModuleCat.hom_ext_iff.mp (hd n)
    have h := LinearMap.congr_fun h x.val
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
    rw [hx, map_zero] at h
    have hs : (-1 : A) ^ (n + 1) •
        (P.complex.d (n + 1) n ≫ (e n).hom x.val) = 0 := h.symm
    have hu : IsUnit ((-1 : A) ^ (n + 1)) := (isUnit_neg_one).pow _
    exact hu.smul_eq_zero.mp hs
  let F : LinearMap.ker S.g.hom →ₗ[A] Abelian.Ext X Y n :=
    { toFun := fun x ↦ P.extMk ((e n).hom x.val) (n + 1) rfl (hc x)
      map_add' := by
        intro x y
        simpa using (P.add_extMk ((e n).hom x.val) ((e n).hom y.val)
          (n + 1) rfl (hc x) (hc y)).symm
      map_smul' := by
        intro a x
        rw [Abelian.Ext.smul_eq_comp_mk₀, P.extMk_comp_mk₀]
        congr 1
        simp }
  have hsurj : Function.Surjective F := by
    intro z
    obtain ⟨f, hf, rfl⟩ := P.extMk_surjective z (n + 1) rfl
    let x := (e n).inv f
    have hx : S.g x = 0 := by
      change L.d n ((ComplexShape.up ℕ).next n) x = 0
      rw [hn]
      apply (ModuleCat.mono_iff_injective (e (n + 1)).hom).mp inferInstance
      have h := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (hd n)) x
      simpa [S, HomologicalComplex.shortComplexFunctor_obj_g, hn, x, hf] using h
    exact ⟨⟨x, hx⟩, by simp [F, x]⟩
  have hker : LinearMap.ker F = LinearMap.range S.moduleCatToCycles := by
    ext x
    change F x = 0 ↔ ∃ y, S.moduleCatToCycles y = x
    cases n with
    | zero =>
      have hf0 : S.f = 0 := by
        change L.d ((ComplexShape.up ℕ).prev 0) 0 = 0
        exact L.shape _ _ (by simp [ComplexShape.up_Rel])
      have hb0 : S.moduleCatToCycles = 0 := by
        ext y
        change S.f y = 0
        rw [hf0]
        rfl
      rw [hb0]
      change P.extMk ((e 0).hom x.val) 1 rfl (hc x) = 0 ↔ ∃ y, 0 = x
      rw [extMk_zero_iff A]
      constructor
      · intro hx
        have hx0 : x = 0 := by
          apply Subtype.ext
          apply (e 0).toLinearEquiv.injective
          change (e 0).hom x.val = (e 0).hom 0
          simpa only [map_zero] using hx
        exact ⟨0, hx0.symm⟩
      · rintro ⟨y, hx⟩
        rw [← hx]
        simp
    | succ p =>
      have hp : (ComplexShape.up ℕ).prev (p + 1) = p :=
        (ComplexShape.up ℕ).prev_eq' (by rfl)
      simp only [Subtype.ext_iff]
      change P.extMk ((e (p + 1)).hom x.val) (p + 1 + 1) rfl (hc x) = 0 ↔
        ∃ y : L.X ((ComplexShape.up ℕ).prev (p + 1)),
          L.d ((ComplexShape.up ℕ).prev (p + 1)) (p + 1) y = x.val
      rw [hp]
      rw [P.extMk_eq_zero_iff _ _ _ _ p rfl]
      constructor
      · rintro ⟨g, hg⟩
        let y := (e p).inv ((-1 : A) ^ (p + 1) • g)
        refine ⟨y, ?_⟩
        apply (e (p + 1)).toLinearEquiv.injective
        have h := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (hd p)) y
        have he : (e p).hom y = (-1 : A) ^ (p + 1) • g := by simp [y]
        change (e (p + 1)).hom (L.d p (p + 1) y) =
          (-1 : A) ^ (p + 1) • (P.complex.d (p + 1) p ≫ (e p).hom y) at h
        rw [he, Linear.comp_smul, smul_smul, ← mul_pow, neg_one_mul,
          neg_neg, one_pow, one_smul, hg] at h
        exact h
      · rintro ⟨y, hy⟩
        refine ⟨(-1 : A) ^ (p + 1) • (e p).hom y, ?_⟩
        have h := LinearMap.congr_fun (ModuleCat.hom_ext_iff.mp (hd p)) y
        simpa [hy, Linear.comp_smul] using h.symm
  let q := F.quotKerEquivOfSurjective hsurj
  let H := (S.moduleCatHomologyIso.toLinearEquiv).symm
  exact ⟨q.symm.trans ((Submodule.quotEquivOfEq _ _ hker).trans H)⟩

end CategoryTheory.ProjectiveResolution
