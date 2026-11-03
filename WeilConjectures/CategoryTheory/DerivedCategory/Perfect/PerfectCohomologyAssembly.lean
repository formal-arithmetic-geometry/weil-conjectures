/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
import WeilConjectures.CategoryTheory.TruncationTriangle
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.PerfectRingTriangleClosure

/-!
# Perfectness from bounded perfect cohomology

Source: Stacks Project, More on Algebra, Tag 066U, lemma-cohomology-perfect
(blueprint: lem-sf-perfect-cohomology-assembly).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open CategoryTheory.Pretriangulated

namespace DerivedCategory

private lemma perfect_of_iso {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    {K L : DerivedCategory (ModuleCat.{u} A)} (h : IsPerfectRingComplex K)
    (e : K ≅ L) : IsPerfectRingComplex L := by
  obtain ⟨P, a, b, ha, hb, hP, ⟨eP⟩⟩ := h
  exact ⟨P, a, b, ha, hb, hP, ⟨e.symm ≪≫ eP⟩⟩

private lemma perfect_shift {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    {K : DerivedCategory (ModuleCat.{u} A)} (h : IsPerfectRingComplex K) (n : ℤ) :
    IsPerfectRingComplex (K⟦n⟧) := by
  obtain ⟨P, a, b, ha, hb, hP, ⟨e⟩⟩ := h
  have := P.isStrictlyGE_shift a n (a - n) (by omega)
  have := P.isStrictlyLE_shift b n (b - n) (by omega)
  refine ⟨P⟦n⟧, a - n, b - n, inferInstance, inferInstance, ?_, ?_⟩
  · exact fun i ↦ hP (i + n)
  · exact ⟨(shiftFunctor _ n).mapIso e ≪≫ ((Q.commShiftIso n).app P).symm⟩

private lemma perfect_of_isZero {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    {K : DerivedCategory (ModuleCat.{u} A)} (h : IsZero K) :
    IsPerfectRingComplex K := by
  refine ⟨0, 0, 0, inferInstance, inferInstance, ?_, ?_⟩
  · intro i
    have : Subsingleton ((0 : CochainComplex (ModuleCat.{u} A) ℤ).X i) :=
      ModuleCat.isZero_iff_subsingleton.mp
        ((HomologicalComplex.eval _ _ i).map_isZero (isZero_zero _))
    constructor <;> infer_instance
  · exact ⟨h.iso (Q.map_isZero (isZero_zero _))⟩

/-- An object with bounded cohomology, each cohomology module being perfect in degree zero,
is perfect. Source: Stacks Project, More on Algebra, Tag 066U, lemma-cohomology-perfect
(blueprint: lem-sf-perfect-cohomology-assembly).

Proof plan:
1. Choose a complex C representing K and fix its derived isomorphism and the induced
   identifications of cohomology, using def-weil-abstract-derived-category. Choose cohomology
   bounds a, b, and put K_r = Q(tau_{<=r} C). Directly computing the canonical truncation gives
   H^i(K_r) = H^i(K) for i <= r and zero otherwise (lem-weil-pbc-truncation-triangle).
2. K_{a-1} is acyclic, hence isomorphic to the zero complex and perfect by
   def-pc-perfect-ring-complex. This also handles the case of entirely zero cohomology.
3. For each r in [a,b], shift a bounded finite-projective model of H^r(K)[0] by -r.
   Its terms remain finite projective, its bounds shift by r, and Q commutes with shifts.
   Thus H^r(K)[-r] is perfect, without requiring uniform resolution bounds over all integers.
4. The canonical truncation triangle of lem-weil-pbc-truncation-triangle has first term
   K_{r-1}, second term K_r, and third term H^r(C)[-r]. The fixed cohomology identifications
   identify this third term with H^r(K)[-r]. Induct over the finite interval [a,b], applying
   lem-sf-perfect-ring-triangle-closure to obtain perfectness of K_r at each step.
5. The inclusion tau_{<=b} C -> C is a quasi-isomorphism because it is the identity on
   cohomology in degrees <= b and both cohomologies vanish above b. Localize and compose
   with the fixed representative isomorphism to obtain K_b isomorphic to K. Transport the
   bounded finite-projective model of K_b to K, as in def-pc-perfect-ring-complex. -/
theorem isPerfectRingComplex_of_perfect_cohomology {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)] (K : DerivedCategory (ModuleCat.{u} A))
    (hbounded : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((homologyFunctor (ModuleCat.{u} A) i).obj K))
    (hperfect : ∀ i : ℤ, IsPerfectRingComplex
      ((singleFunctor (ModuleCat.{u} A) 0).obj
        ((homologyFunctor (ModuleCat.{u} A) i).obj K))) :
    IsPerfectRingComplex K := by
  obtain ⟨a, b, hbounded⟩ := hbounded
  let C := Q.objPreimage K
  let e : Q.obj C ≅ K := Q.objObjPreimageIso K
  have hCGE : C.IsGE a := by
    rw [← isGE_Q_obj_iff, isGE_iff]
    intro i hi
    exact (hbounded i (Or.inl hi)).of_iso ((homologyFunctor _ i).mapIso e)
  have hCLE : C.IsLE b := by
    rw [← isLE_Q_obj_iff, isLE_iff]
    intro i hi
    exact (hbounded i (Or.inr hi)).of_iso ((homologyFunctor _ i).mapIso e)
  have hsingle (r : ℤ) : IsPerfectRingComplex
      (Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} A) r).obj (C.homology r))) := by
    let eH : C.homology r ≅ (homologyFunctor (ModuleCat.{u} A) r).obj K :=
      ((homologyFunctorFactors _ r).app C).symm ≪≫ (homologyFunctor _ r).mapIso e
    have h₀ := perfect_of_iso (hperfect r) ((singleFunctor _ 0).mapIso eH.symm)
    have hr := perfect_shift h₀ (-r)
    exact perfect_of_iso hr
      (((singleFunctors (ModuleCat.{u} A)).shiftIso (-r) r 0 (by omega)).app
        (C.homology r))
  have key (n : ℕ) : IsPerfectRingComplex (Q.obj (C.truncLE (a + n - 1))) := by
    induction n with
    | zero =>
      have hGE : (C.truncLE (a - 1)).IsGE a :=
        (((truncation_triangle (ModuleCat.{u} A) (a - 1)).2.2 C a).2 hCGE).2.1
      have hZ : IsZero (Q.obj (C.truncLE (a - 1))) := by
        rw [IsZero.iff_id_eq_zero]
        exact TStructure.t.zero (𝟙 _) (a - 1) a (by omega)
      simpa using perfect_of_isZero hZ
    | succ n ih =>
      obtain ⟨i, j, _, _, k, hk, _⟩ :=
        (truncation_triangle (ModuleCat.{u} A) (a + n)).1 C
      have hi : IsPerfectRingComplex (Q.obj (C.truncLE (a + n - 1))) := ih
      have hstep := isPerfectRingComplex_obj₂_of_distTriang
        (Triangle.mk (Q.map i) (Q.map j) k) hk hi (hsingle (a + n))
      convert hstep using 1
      congr 2
      omega
  have hlast := key (b + 1 - a).toNat
  by_cases hab : a ≤ b + 1
  · have hn : a + ((b + 1 - a).toNat : ℤ) - 1 = b := by omega
    rw [hn] at hlast
    have : QuasiIso (C.ιTruncLE b) := (CochainComplex.quasiIso_ιTruncLE_iff C b).2 hCLE
    exact perfect_of_iso hlast (asIso (Q.map (C.ιTruncLE b)) ≪≫ e)
  · have hZ : IsZero (Q.obj C) := by
      rw [IsZero.iff_id_eq_zero]
      exact TStructure.t.zero (𝟙 _) b a (by omega)
    exact perfect_of_iso (perfect_of_isZero hZ) e

end DerivedCategory
