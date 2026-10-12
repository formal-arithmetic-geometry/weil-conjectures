/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Right derived functors of bounded complexes with homology in a weak Serre subcategory

Let `G : C ⥤ D` be an additive functor between abelian categories, `C` with K-injective
resolutions, let `P_C` be a property of objects of `C` and `P_D` a weak Serre subcategory of
`D` (closed under kernels, cokernels and extensions). Suppose that for every `X` satisfying
`P_C` all the classical derived functors `RᵠG X` satisfy `P_D`, and vanish for `q > c`.
Then for every `K ∈ D(C)` with homology concentrated in `[a, b]` and satisfying `P_C`, the
total derived functor `RG K` has homology satisfying `P_D`, concentrated in `[a, b + c]`
(`CategoryTheory.Functor.rightDerivedFunctor_obj_homologyProperty`).

This is the abstract form of blueprint `prop-weil-pbc-restriction-direct-image`. The blueprint
argues with the spectral sequence `E₂^{p,q} = RᵖG Hᵠ(K) ⇒ H^{p+q}(RG K)` of the truncation couple
and the finite filtration of its abutment; here the same dévissage is carried out directly, by
induction on the length of the interval `[a, b]`, along the truncation triangles
`τ_{< b} K ⟶ K ⟶ H^b(K)[-b] ⟶` (`DerivedCategory.prop_of_homologyConcentratedIn`), which is
the finite filtration induction underlying the convergence of that spectral sequence.

-/

@[expose] public section

open CategoryTheory Abelian Limits Pretriangulated

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

open TStructure (t)

/-- **Dévissage of complexes with homology in an interval.** Let `Q` be a property of objects of
`D(C)` containing zero, closed under isomorphisms and extensions (in distinguished triangles), and
let `P` be a property of objects of `C` such that `Q` contains every `X` satisfying `P` placed in
a degree `q ∈ [a, b]`. Then `Q` contains every object of `D(C)` whose homology is concentrated in
`[a, b]` and satisfies `P` there. -/
lemma prop_of_homologyConcentratedIn (Q : ObjectProperty (DerivedCategory C))
    [Q.IsTriangulatedClosed₂] [Q.IsClosedUnderIsomorphisms] [Q.ContainsZero]
    (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms] (a b : ℤ)
    (hP : ∀ X q, a ≤ q → q ≤ b → P X → Q ((singleFunctor C q).obj X))
    (M : DerivedCategory C) (hM : homologyConcentratedIn a b M)
    (hMP : ∀ q, a ≤ q → q ≤ b → P ((homologyFunctor C q).obj M)) : Q M := by
  suffices H : ∀ (n : ℕ) (M : DerivedCategory C), M.IsGE a → M.IsLE (a + n - 1) →
      a + n - 1 ≤ b → (∀ q, a ≤ q → q < a + n → P ((homologyFunctor C q).obj M)) → Q M by
    obtain ⟨h₁, h₂⟩ := hM
    by_cases hab : a ≤ b
    · have : M.IsLE (a + ↑(b - a + 1).toNat - 1) := t.isLE_of_le M b _ (by lia)
      exact H (b - a + 1).toNat M h₁ this (by lia) fun q hq hq' ↦ hMP q hq (by lia)
    · exact Q.prop_of_isZero (t.isZero M b a (by lia))
  intro n
  induction n with
  | zero =>
    intro M _ _ _ _
    have : M.IsLE (a - 1) := by simpa using ‹M.IsLE (a + ↑(0 : ℕ) - 1)›
    exact Q.prop_of_isZero (t.isZero M (a - 1) a (by lia))
  | succ n ih =>
    intro M _ _ hb hM
    set b' : ℤ := a + n
    have hT := t.triangleLTGE_distinguished b' M
    -- the third term is `H^{b'} M` placed in degree `b'`
    have : ((t.triangleLTGE b').obj M).obj₃.IsLE b' := by
      have : M.IsLE b' := t.isLE_of_le M (a + ↑(n + 1) - 1) _ (by lia)
      exact inferInstanceAs (t.IsLE ((t.truncGE b').obj M) b')
    have : ((t.triangleLTGE b').obj M).obj₃.IsGE b' := by
      infer_instance
    obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE
      ((t.triangleLTGE b').obj M).obj₃ b'
    have h₁ : IsZero ((homologyFunctor C (b' + 1)).obj ((t.triangleLTGE b').obj M).obj₁) :=
      isZero_of_isLE _ (b' - 1) _ (by lia)
    have h₀ : IsZero ((homologyFunctor C b').obj ((t.triangleLTGE b').obj M).obj₁) :=
      isZero_of_isLE _ (b' - 1) _ (by lia)
    have := isIso_homologyMap_mor₂ _ hT b' (b' + 1) rfl h₀ h₁
    have hY : P Y := P.prop_of_iso
      (asIso ((homologyFunctor C b').map ((t.triangleLTGE b').obj M).mor₂) ≪≫
        (homologyFunctor C b').mapIso e ≪≫ (singleFunctorCompHomologyFunctorIso C b').app Y)
      (hM b' (by lia) (by lia))
    have h₃ : Q ((t.triangleLTGE b').obj M).obj₃ :=
      Q.prop_of_iso e.symm (hP Y b' (by lia) (by lia) hY)
    -- the first term is handled by induction
    have h₁ : Q ((t.triangleLTGE b').obj M).obj₁ := by
      refine ih _ ?_ ?_ (by lia) fun q hq hq' ↦ ?_
      · exact inferInstanceAs (t.IsGE ((t.truncLT b').obj M) a)
      · exact t.isLE_truncLT_obj _ _ _ (by lia)
      · have : IsIso ((homologyFunctor C q).map ((t.triangleLTGE b').obj M).mor₁) :=
          isIso_homologyMap_mor₁ _ hT (q - 1) q (by lia)
            (isZero_of_isGE _ b' _ (by lia)) (isZero_of_isGE _ b' _ (by lia))
        exact P.prop_of_iso
          (asIso ((homologyFunctor C q).map ((t.triangleLTGE b').obj M).mor₁)).symm
          (hM q hq (by lia))
    exact Q.ext_of_isTriangulatedClosed₂ _ hT h₁ h₃

end DerivedCategory

namespace CategoryTheory.Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  (G : C ⥤ D) [G.Additive] [EnoughInjectives C] [HasKInjectiveResolutions C]

open DerivedCategory TStructure

/-- The total right derived functor of an object `X` placed in degree `0`: if every classical
derived functor `RᵠG X` satisfies a property `P` of objects of `D` containing zero and closed
under isomorphisms, and `RᵠG X = 0` for `q > c`, then `RG(X[0])` has homology satisfying `P`,
concentrated in `[0, c]`. -/
lemma rightDerivedFunctor_obj_singleFunctor_homologyProperty (P : ObjectProperty D)
    [P.ContainsZero] [P.IsClosedUnderIsomorphisms] (c : ℕ) (X : C)
    (h₁ : ∀ q : ℕ, P ((G.rightDerived q).obj X))
    (h₂ : ∀ q : ℕ, c < q → IsZero ((G.rightDerived q).obj X)) :
    homologyProperty P (G.rightDerivedFunctor.obj ((singleFunctor C 0).obj X)) ∧
      homologyConcentratedIn 0 c (G.rightDerivedFunctor.obj ((singleFunctor C 0).obj X)) := by
  have hge := G.isGE_rightDerivedFunctor_obj_singleFunctor X
  refine ⟨fun n ↦ ?_, hge, ?_⟩
  · obtain ⟨k, rfl⟩ | hn := Int.eq_nat_or_neg n
    · exact P.prop_of_iso (G.homologyRightDerivedFunctorObjSingleFunctorIso X k).symm (h₁ k)
    · by_cases hk : (k : ℤ) = 0
      · obtain rfl : k = 0 := by exact_mod_cast hk
        exact P.prop_of_iso (G.homologyRightDerivedFunctorObjSingleFunctorIso X 0).symm (h₁ 0)
      · obtain ⟨k, rfl⟩ := hn
        exact P.prop_of_isZero (isZero_of_isGE _ 0 _ (by lia))
  · refine (isLE_iff _ c).2 fun n hn ↦ ?_
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = k := ⟨n.toNat, by lia⟩
    exact (h₂ k (by exact_mod_cast hn)).of_iso
      (G.homologyRightDerivedFunctorObjSingleFunctorIso X k)

/-- Blueprint `prop-weil-pbc-restriction-direct-image` (abstract form): **the right derived
functor of a bounded complex with homology in a weak Serre subcategory.**

Let `P_C` be a property of objects of `C`, and `P_D` a property of objects of `D` containing
zero and closed under isomorphisms, kernels, cokernels and extensions. Suppose that for every
`X` satisfying `P_C`, every `RᵠG X` satisfies `P_D` and `RᵠG X = 0` for `q > c`. If `K ∈ D(C)`
has homology concentrated in `[a, b]`, all satisfying `P_C`, then `RG K` has homology satisfying
`P_D`, concentrated in `[a, b + c]`. -/
theorem rightDerivedFunctor_obj_homologyProperty (PC : ObjectProperty C)
    [PC.IsClosedUnderIsomorphisms] (PD : ObjectProperty D) [PD.ContainsZero]
    [PD.IsClosedUnderIsomorphisms] [PD.IsClosedUnderKernels] [PD.IsClosedUnderCokernels]
    [PD.IsClosedUnderExtensions] (c : ℕ)
    (h₁ : ∀ X, PC X → ∀ q : ℕ, PD ((G.rightDerived q).obj X))
    (h₂ : ∀ X, PC X → ∀ q : ℕ, c < q → IsZero ((G.rightDerived q).obj X))
    (a b : ℤ) (K : DerivedCategory C) (hK : homologyConcentratedIn a b K)
    (hKP : homologyProperty PC K) :
    homologyProperty PD (G.rightDerivedFunctor.obj K) ∧
      homologyConcentratedIn a (b + c) (G.rightDerivedFunctor.obj K) := by
  let Q : ObjectProperty (DerivedCategory C) := fun M ↦
    homologyProperty PD (G.rightDerivedFunctor.obj M) ∧
      homologyConcentratedIn a (b + c) (G.rightDerivedFunctor.obj M)
  have : Q.IsClosedUnderIsomorphisms := ⟨fun e ⟨h, h', h''⟩ ↦
    ⟨(homologyProperty PD).prop_of_iso (G.rightDerivedFunctor.mapIso e) h,
      t.isGE_of_iso (G.rightDerivedFunctor.mapIso e) a,
      t.isLE_of_iso (G.rightDerivedFunctor.mapIso e) (b + c)⟩⟩
  have : Q.ContainsZero := ⟨⟨0, isZero_zero _, by
    have h := G.isZero_rightDerivedFunctor_obj (isZero_zero (DerivedCategory C))
    exact ⟨(homologyProperty PD).prop_of_isZero h, t.isGE_of_isZero h a,
      t.isLE_of_isZero h (b + c)⟩⟩⟩
  have : Q.IsTriangulatedClosed₂ := .mk' fun T hT ⟨h₁, h₁', h₁''⟩ ⟨h₃, h₃', h₃''⟩ ↦ by
    have hT' := G.rightDerivedFunctor.map_distinguished T hT
    refine ⟨(homologyProperty PD).ext_of_isTriangulatedClosed₂ _ hT' h₁ h₃,
      t.isGE₂ _ hT' a h₁' h₃', t.isLE₂ _ hT' (b + c) h₁'' h₃''⟩
  refine prop_of_homologyConcentratedIn Q PC a b (fun X q hq hq' hX ↦ ?_) K hK
    fun q _ _ ↦ hKP q
  obtain ⟨hP, hge, hle⟩ := G.rightDerivedFunctor_obj_singleFunctor_homologyProperty PD c X
    (h₁ X hX) (h₂ X hX)
  -- `RG(X[-q]) ≅ RG(X[0])[-q]`
  let e : G.rightDerivedFunctor.obj ((singleFunctor C q).obj X) ≅
      (G.rightDerivedFunctor.obj ((singleFunctor C 0).obj X))⟦-q⟧ :=
    G.rightDerivedFunctor.mapIso (((singleFunctors C).shiftIso (-q) q 0 (by lia)).app X).symm ≪≫
      (G.rightDerivedFunctor.commShiftIso (-q)).app _
  refine ⟨(homologyProperty PD).prop_of_iso e.symm ((homologyProperty PD).le_shift (-q) _ hP),
    ?_, ?_⟩
  · have := t.isGE_shift (G.rightDerivedFunctor.obj ((singleFunctor C 0).obj X)) 0 (-q) q
    have := t.isGE_of_iso e.symm q
    exact t.isGE_of_ge _ a q hq
  · have := t.isLE_shift (G.rightDerivedFunctor.obj ((singleFunctor C 0).obj X)) c (-q) (c + q)
    have := t.isLE_of_iso e.symm (c + q)
    exact t.isLE_of_le _ (c + q) (b + c) (by lia)

end CategoryTheory.Functor
