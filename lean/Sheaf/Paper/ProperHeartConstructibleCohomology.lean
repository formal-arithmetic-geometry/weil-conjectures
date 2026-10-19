/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K5
-/
module

public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.Paper.FiniteCoefficientDescentTwoColimit
import Sheaf.Paper.ProperBaseChangeRational

/-!
# Constructibility of proper higher direct images with rational coefficients

Source: blueprint main-20261015, sk-lem-proper-heart-bound, final paragraph
(blueprint: lem-proper-heart-constructible-cohomology).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

-- Step 1: use the identity cover and the zero finitely presented condensed module.
private lemma finiteConstantLocalModel_of_isZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : HasFiniteConstantLocalModel Λ X M := by
  refine ⟨.singleton (𝟙 X) (Precoverage.mem_coverings_of_isIso _), fun i ↦ ?_⟩
  refine ⟨HasZeroObject.zero.choose, ?_, ⟨?_⟩⟩
  · exact ⟨0, 0, 𝟙 _, ⟨(isZero_zero _).iso (isZero_cokernel_of_epi (𝟙 _))⟩⟩
  · exact ((CondensedRing.upperStar Λ _).map_isZero hM).iso
      (((upperStarFromPoint _).mapMod Λ).map_isZero (isZero_zero _))

-- The one-stratum stratification works also when the scheme is empty.
private lemma finiteConstantStratified_of_isZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : IsFiniteConstantStratified Λ X M := by
  let S : Scheme.Stratification X :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ isOpen_univ.isLocallyClosed
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := Set.iUnion_const _
      pairwise_disjoint_stratum := fun i j hij ↦ (hij (Subsingleton.elim i j)).elim
      domain := fun _ ↦ X
      immersion := fun _ ↦ 𝟙 X
      range_immersion := fun _ ↦ Set.range_id' }
  exact ⟨S, fun a ↦ finiteConstantLocalModel_of_isZero Λ _ _
    ((CondensedRing.upperStar Λ (S.immersion a)).map_isZero hM)⟩

private lemma constantModelConstructible_of_isZero
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsZero M) : IsConstantModelConstructible Λ X M := by
  classical
  unfold IsConstantModelConstructible
  split
  · exact finiteConstantStratified_of_isZero Λ X M hM
  · exact fun U _ ↦ finiteConstantStratified_of_isZero Λ _ _
      ((CondensedRing.upperStar Λ U.ι).map_isZero hM)

private lemma constantModelConstructible_of_iso
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    {M N : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)}
    (e : M ≅ N) (hM : IsConstantModelConstructible Λ X M) :
    IsConstantModelConstructible Λ X N := by
  have hs (T : Scheme.{u})
      {A B : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ T)}
      (e : A ≅ B) (hA : IsFiniteConstantStratified Λ T A) :
      IsFiniteConstantStratified Λ T B := by
    obtain ⟨S, hS⟩ := hA
    refine ⟨S, fun a ↦ ?_⟩
    obtain ⟨𝒰, h𝒰⟩ := hS a
    refine ⟨𝒰, fun i ↦ ?_⟩
    obtain ⟨P, hP, ⟨eP⟩⟩ := h𝒰 i
    exact ⟨P, hP, ⟨((CondensedRing.upperStar Λ (𝒰.f i)).mapIso
      ((CondensedRing.upperStar Λ (S.immersion a)).mapIso e)).symm ≪≫ eP⟩⟩
  classical
  unfold IsConstantModelConstructible at *
  split_ifs at * with h
  · exact hs X e hM
  · exact fun U hU ↦ hs U.toScheme ((CondensedRing.upperStar Λ U.ι).mapIso e) (hM U hU)

private lemma constantModelConstructible_single
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))
    (hM : IsConstantModelConstructible Λ X M) :
    constantModelBoundedConstructible Λ X ((DerivedCategory.singleFunctor _ 0).obj M) := by
  refine ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun n ↦ ?_⟩
  by_cases hn : n = 0
  · subst n
    exact constantModelConstructible_of_iso Λ X
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M).symm hM
  · apply constantModelConstructible_of_isZero
    rcases lt_or_gt_of_ne hn with hn | hn
    · exact DerivedCategory.isZero_of_isGE _ 0 n hn
    · exact DerivedCategory.isZero_of_isLE _ 0 n hn

private lemma constantModelBoundedConstructible_eq_rational
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})) [IsCommMonObj Λ.X]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Λ = Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ))
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (T : Scheme.{u}) [T.Over (Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))] :
    constantModelBoundedConstructible Λ.X T = boundedConstructible (condensedRingObj Λ.X T) := by
  have h := (finiteCoefficientDescentTwoColimit k p₀ ℓ hp₀ hpℓ T).2.2.2
  rcases hΛ with ⟨E, hE⟩ | hQ
  · subst Λ
    exact (h.1 E).1
  · subst Λ
    exact h.2.1.1

attribute [local irreducible] Functor.rightDerivedFunctor

/-- Proper higher direct images of finite constant-model constructible rational modules
are again finite constant-model constructible, for finite extensions and the condensed
algebraic closure.

Source: blueprint main-20261015, sk-lem-proper-heart-bound, final paragraph, first sentence;
sk-thm-sfb-proper-base-change, rational bounded-constructibility clause
(blueprint: lem-proper-heart-constructible-cohomology).

Proof: place M in degree zero. Its degree-zero cohomology is isomorphic to M;
all other cohomology modules are zero. Transport finite constant local models through
the isomorphism and use the rank-zero constant model for zero modules, obtaining
finite-constant-model bounded constructibility. In the standing finite-type setting,
clause (4) of finiteCoefficientDescentTwoColimit identifies this predicate with the
boundedConstructible predicate for both rational coefficient rings. Use that equality
on X, apply properPushforward_boundedConstructible_rational to the actual morphism
over Spec k, and use the equality on Y in the reverse direction. Extract degree q.
The zero module and empty schemes are included by the same construction. No uniform
fibre dimension bound or passage to ind-objects is used. -/
theorem properHeart_constructible_cohomology
    (ℓ : ℕ) [Fact ℓ.Prime]
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]
    (hΛ : (∃ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Mon.mk Λ = Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Mon.mk Λ = Mon.mk (Profinite.padicAlgClRingObj ℓ))
    (k : Type u) [Field k] (p₀ : ℕ) [CharP k p₀] (hp₀ : 0 < p₀) (hpℓ : p₀ ≠ ℓ)
    (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))] [LocallyOfFiniteType (X ↘ Spec (.of k))]
    [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))] [LocallyOfFiniteType (Y ↘ Spec (.of k))]
    [QuasiCompact (Y ↘ Spec (.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (.of k))] [IsProper p] :
    ∀ M, IsConstantModelConstructible Λ X M → ∀ q : ℤ, 0 ≤ q →
      IsConstantModelConstructible Λ Y ((DerivedCategory.homologyFunctor _ q).obj
        ((CondensedRing.lowerStar Λ p).rightDerivedFunctor.obj
          ((DerivedCategory.singleFunctor _ 0).obj M))) := by
  have hEq (T : Scheme.{u}) [T.Over (Spec (.of k))]
      [IsSeparated (T ↘ Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
      [QuasiCompact (T ↘ Spec (.of k))] :
      constantModelBoundedConstructible Λ T = boundedConstructible (condensedRingObj Λ T) :=
    constantModelBoundedConstructible_eq_rational ℓ (Mon.mk Λ) hΛ k p₀ hp₀ hpℓ T
  have : Fact (ringChar k).Prime := ⟨by
    rw [ringChar.eq k p₀]
    exact (CharP.char_is_prime_or_zero k p₀).resolve_right hp₀.ne'⟩
  have : Fact (ringChar k ≠ ℓ) := ⟨by rw [ringChar.eq k p₀]; exact hpℓ⟩
  intro M hM q _
  have hK := constantModelConstructible_single Λ X M hM
  have hK' := (congrFun (hEq X) _).mp hK
  let XOver := Over.mk (X ↘ Spec (.of k))
  let YOver := Over.mk (Y ↘ Spec (.of k))
  have : LocallyOfFiniteType XOver.hom :=
    inferInstanceAs (LocallyOfFiniteType (X ↘ Spec (.of k)))
  have : QuasiCompact XOver.hom := inferInstanceAs (QuasiCompact (X ↘ Spec (.of k)))
  have : IsSeparated XOver.hom := inferInstanceAs (IsSeparated (X ↘ Spec (.of k)))
  have : LocallyOfFiniteType YOver.hom :=
    inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of k)))
  have : QuasiCompact YOver.hom := inferInstanceAs (QuasiCompact (Y ↘ Spec (.of k)))
  have : IsSeparated YOver.hom := inferInstanceAs (IsSeparated (Y ↘ Spec (.of k)))
  let pOver : XOver ⟶ YOver := Over.homMk p
  have : IsProper pOver.left := inferInstanceAs (IsProper p)
  have hP := CondensedRing.properPushforward_boundedConstructible_rational ℓ
    (k := k) (X := XOver) (Y := YOver) pOver (Mon.mk Λ) hΛ _ hK'
  exact ((congrFun (hEq Y) _).mpr hP).2 q

end AlgebraicGeometry.ProEtale
