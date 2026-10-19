/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.RingTheory.FiniteProjectiveComplexFreeModel
import WeilConjectures.RingTheory.RingPseudoCoherentLocalizationGlue
import WeilConjectures.Algebra.Homology.TorAmplitudeFlatModel
import WeilConjectures.CategoryTheory.DerivedCategory.RingPseudoCoherentFiniteTorPerfect
import Sheaf.Algebra.Homology.TorAmplitudePrincipalCover

/-!
# Perfect complexes glue over finite principal covers

Source: Stacks Project, More on Algebra, Tag 066Y, lemma-glue-perfect
(blueprint: lem-weil-pbc-perfect-ring-principal-cover-glue).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace DerivedCategory

/-- Perfectness descends across a finite principal cover, including the empty cover.
The functors `L i`, with universal counits `ε i`, are derived extension of scalars
along `R → R[1 / f i]`. Their universal property specifies the usual derived scalar
extension independently of a choice of resolution.

Source: Stacks Project, More on Algebra, Tag 066Y, lemma-glue-perfect
(blueprint: lem-weil-pbc-perfect-ring-principal-cover-glue).

Proof:
1. Choose a complex representing `C`. Localization is flat
   (lem-weil-pbc-localization-flat), so extension of scalars is exact
   (lem-weil-pbc-flat-tensor-exact). Mathlib's `mapDerivedCategory` computes its
   derived functor termwise. Uniqueness of left derived functors compares it with
   the supplied `L i`, so local perfectness applies to the termwise localization.
2. Replace each bounded finite-projective local model by a bounded-above finite-free
   model using lem-pc-finite-projective-complex-free-model. These witness local
   pseudo-coherence (def-pc-ring-pseudo-coherent-complex); descend it by
   lem-pc-ring-pseudo-coherent-localization-glue.
3. Projective modules are flat (lem-weil-pbc-projective-module-flat). Apply the
   bounded-flat-model implication of lem-pc-module-tor-amplitude-flat-model to obtain
   ordered local Tor intervals. The finite ranges of their endpoints have a common
   lower bound `a` and upper bound `b`, even for the empty family. Widen every local
   interval to `[min a 0, max b 0]`, which is ordered because it contains zero.
4. Descend these common bounds by lem-weil-pbc-tor-amplitude-principal-cover-glue.
5. Apply lem-pc-ring-pseudo-coherent-finite-tor-perfect to pseudo-coherence and the
   global Tor bounds. Convert its termwise vanishing to strict complex bounds.
   Its bounded finite-projective model witnesses `IsPerfect C`. -/
theorem isPerfect_of_principal_cover
    {R : Type u} [CommRing R] [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    (C : DerivedCategory (ModuleCat.{u} R)) (r : ℕ) (f : Fin r → R)
    [∀ i : Fin r, HasDerivedCategory.{u} (ModuleCat.{u} (Localization.Away (f i)))]
    (hf : ∃ v : Fin r → R, ∑ i : Fin r, v i * f i = 1)
    (L : ∀ i : Fin r, DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} (Localization.Away (f i))))
    (ε : ∀ i : Fin r, Qh ⋙ L i ⟶
      @Functor.mapHomotopyCategory _ _ _ _ _ _ _
        (ModuleCat.extendScalars (algebraMap R (Localization.Away (f i))))
        (ModuleCat.extendRestrictScalarsAdj
          (algebraMap R (Localization.Away (f i)))).left_adjoint_additive (.up ℤ) ⋙ Qh)
    [∀ i : Fin r, (L i).IsLeftDerivedFunctor (ε i)
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ))]
    (hlocal : ∀ i : Fin r, IsPerfect ((L i).obj C)) : IsPerfect C := by
  classical
  let K := (Q : CochainComplex (ModuleCat.{u} R) ℤ ⥤ _).objPreimage C
  let e : Q.obj K ≅ C := Q.objObjPreimageIso C
  let E (i : Fin r) := ModuleCat.extendScalars (algebraMap R (Localization.Away (f i)))
  let Kloc (i : Fin r) := ((E i).mapHomologicalComplex (.up ℤ)).obj K
  have hperfect (i : Fin r) : IsPerfect (Q.obj (Kloc i)) := by
    have : (E i).Additive :=
      (ModuleCat.extendRestrictScalarsAdj
        (algebraMap R (Localization.Away (f i)))).left_adjoint_additive
    have : CategoryTheory.Limits.PreservesFiniteLimits (E i) :=
      ModuleCat.preservesFiniteLimits_extendScalars_of_flat
        (RingHom.flat_algebraMap_iff.mpr
          (IsLocalization.flat (Localization.Away (f i)) (Submonoid.powers (f i))))
    have : (E i).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj
        (algebraMap R (Localization.Away (f i)))).isLeftAdjoint
    have : (E i).mapDerivedCategory.IsLeftDerivedFunctor
        (E i).mapDerivedCategoryFactorsh.hom
        (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) :=
      Functor.isLeftDerivedFunctor_of_inverts _ _ _
    let δ := Functor.leftDerivedNatIso (L i) (E i).mapDerivedCategory (ε i)
      (E i).mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) (Iso.refl _)
    exact (hlocal i).of_iso
      ((L i).mapIso e.symm ≪≫ δ.app (Q.obj K) ≪≫ (E i).mapDerivedCategoryFactors.app K)
  have hspan : Ideal.span (Set.range f) = ⊤ := by
    apply (Ideal.eq_top_iff_one _).mpr
    obtain ⟨v, hv⟩ := hf
    rw [← hv]
    exact Ideal.sum_mem _ (fun i _ ↦
      Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_range_self i)))
  have hPC : IsPseudoCoherent (Q.obj K) := by
    apply (ringPseudoCoherent_localization_glue 0 K r f hspan).2
    intro i
    obtain ⟨P, _, b, _, hle, hP, ⟨eP⟩⟩ := hperfect i
    obtain ⟨F, hF, hfree, q, hq⟩ :=
      CochainComplex.exists_finiteFree_model_of_finite_projective
        (Localization.Away (f i)) P b hle (fun n ↦ (hP n).2) (fun n ↦ (hP n).1)
    have : QuasiIso q := hq
    exact ⟨F, b, hF, hfree, ⟨asIso (Q.map q) ≪≫ eP.symm⟩⟩
  have hTorLocal (i : Fin r) : ∃ a b : ℤ, a ≤ b ∧
      torAmplitudeIn (ModuleCat.{u} (Localization.Away (f i))) a b (Q.obj (Kloc i)) := by
    obtain ⟨P, a, b, hge, hle, hP, ⟨eP⟩⟩ := hperfect i
    have := hge
    have := hle
    refine ⟨min a b, max a b, ?_, ?_⟩
    · exact le_trans (min_le_left _ _) (le_max_left _ _)
    · apply (module_torAmplitudeIn_iff_exists_flat_model (Kloc i)
        (min a b) (max a b) (le_trans (min_le_left _ _) (le_max_left _ _))).2
      refine ⟨P, ?_, ?_, ⟨eP⟩⟩
      · intro n
        have := (hP n).1
        infer_instance
      · intro n hn
        rcases hn with hn | hn
        · exact P.isZero_of_isStrictlyGE a n (lt_of_lt_of_le hn (min_le_left _ _))
        · exact P.isZero_of_isStrictlyLE b n (lt_of_le_of_lt (le_max_right _ _) hn)
  choose lower upper _ hTor using hTorLocal
  obtain ⟨a, ha⟩ := (Set.finite_range lower).bddBelow
  obtain ⟨b, hb⟩ := (Set.finite_range upper).bddAbove
  have hab : min a 0 ≤ max b 0 := le_trans (min_le_right _ _) (le_max_right _ _)
  have hTorGlobal : torAmplitudeIn (ModuleCat.{u} R) (min a 0) (max b 0) (Q.obj K) := by
    apply torAmplitudeIn_of_principal_cover K (min a 0) (max b 0) hab r f hspan
    intro i
    exact (hTor i).mono
      (le_trans (min_le_left _ _) (ha (Set.mem_range_self i)))
      (le_trans (hb (Set.mem_range_self i)) (le_max_left _ _))
  obtain ⟨P, ⟨c, d, hzero⟩, hfinite, hprojective, ⟨eP⟩⟩ :=
    isPerfect_of_pseudoCoherent_finiteTorAmplitude (Q.obj K) hPC
      ⟨min a 0, max b 0, hab, hTorGlobal⟩
  exact ⟨P, c, d,
    (P.isStrictlyGE_iff c).2 (fun n hn ↦ hzero n (Or.inl hn)),
    (P.isStrictlyLE_iff d).2 (fun n hn ↦ hzero n (Or.inr hn)),
    fun n ↦ ⟨hprojective n, hfinite n⟩, ⟨e.symm ≪≫ eP.symm⟩⟩

end DerivedCategory
