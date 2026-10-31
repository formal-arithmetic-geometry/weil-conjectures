/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.PQFCohomology
public import WeilConjectures.AlgebraicGeometry.Modules.Differentials
public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheaf
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Dual.Defs
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.AlgebraicGeometry.Cohomology.Serre
import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveSpaceOverField
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Canonical
import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveSpaceTwist
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyScalarEndomorphism
import WeilConjectures.AlgebraicGeometry.ExteriorSheafComparison
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.TwistCechMonomialDecomposition
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ExponentCechHomology

/-! # Cohomology and canonical sheaf of projective space over a field

Source: blueprint main-20261015, sec-picard-framework/sk-thm-picard-pn/_section.md;
Stacks Project, Tag 01XT, lemma-cohomology-projective-space-over-ring and equation-identify.
(blueprint: sk-thm-picard-pn)

Cohomology is the right derived functor in module sheaves specified by
`pqf-def-cohomology`, restricted to `k` along the structure morphism. The homogeneous
polynomial submodule realizes the symmetric power in the ordered homogeneous coordinates.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Modules Opposite

private theorem cohomology_linear_comparison (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (Spec (.of k))] (F : X.Modules) (q : ℕ) :
    Nonempty (((ModuleCat.restrictScalars (Scheme.globalSectionsRingHom k (X := X))).obj
      ((RingedSpace.moduleCohomology X.toRingedSpace q).obj F)) ≃ₗ[k] F.H q) := by
  obtain ⟨a, ha⟩ := exists_moduleCohomology_source_comparison X q
  refine ⟨{ a F with map_smul' := ?_ }⟩
  intro c x
  let b := Scheme.globalSectionsRingHom k (X := X) c
  have hn := ha F F (F.smulHom b) x
  have hm := moduleCohomology_scalar_endomorphism F (F.smulHom b) b
    (fun U t ↦ smulHom_app_apply F b U t) q x
  rw [hm] at hn
  exact hn

private theorem standardOpen_eq_top_of_unique (S : Scheme.{u})
    (i : ULift.{u} (Fin 1)) : standardOpen (ULift.{u} (Fin 1)) S i = ⊤ := by
  have h := iSup_standardOpen (ULift.{u} (Fin 1)) S
  simpa only [iSup_unique, Subsingleton.elim (default : ULift.{u} (Fin 1)) i] using h

private theorem zero_dim_isIso (S : Scheme.{u}) :
    IsIso (ℙ(ULift.{u} (Fin 1); S) ↘ S) := by
  let i : ULift.{u} (Fin 1) := ⟨0⟩
  have hU := standardOpen_eq_top_of_unique S i
  have : IsEmpty {j : ULift.{u} (Fin 1) // j ≠ i} :=
    ⟨fun j ↦ j.2 (Subsingleton.elim _ _)⟩
  have hcomp : IsIso ((standardOpen (ULift.{u} (Fin 1)) S i).ι ≫
      ℙ(ULift.{u} (Fin 1); S) ↘ S) := by
    rw [← standardOpenIso_hom_over]
    infer_instance
  have : IsIso (standardOpen (ULift.{u} (Fin 1)) S i).ι := by
    rw [hU, ← Scheme.topIso_hom]
    infer_instance
  exact IsIso.of_isIso_comp_left (standardOpen (ULift.{u} (Fin 1)) S i).ι _

private theorem zero_dim_twist (S : Scheme.{u}) (m : ℤ) :
    Nonempty (twist (ULift.{u} (Fin 1)) S m ≅
      SheafOfModules.unit ℙ(ULift.{u} (Fin 1); S).ringCatSheaf) := by
  refine ⟨isoOfIsFreeGenerator (iSup_standardOpen (ULift.{u} (Fin 1)) S)
    (isFreeGenerator_twistGenerator _ _ m)
    (fun i ↦ isFreeGenerator_one (standardOpen _ S i)) ?_⟩
  intro i j W hi hj a b hab
  have hij : i = j := Subsingleton.elim _ _
  subst j
  have hab' : a = b := ((isFreeGenerator_twistGenerator _ _ m i).map hi).smul_left_injective
    (by simpa only [Subsingleton.elim hj hi] using hab)
  subst b
  rfl

private theorem structure_H_zero (k : Type u) [Field k] (n : ℕ) :
    Nonempty ((Scheme.Modules.unit
      ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))).H 0 ≃ₗ[k] k) := by
  let N := ULift.{u} (Fin (n + 1))
  let e := (cohomologyFunctor k 0).mapIso (unitIsoTwistZero N (Spec (.of k)))
  obtain ⟨a⟩ := nonempty_H_zero_twist_equiv N k n (by simp [N]) 0
  let : Unique {s : N →₀ ℕ | s.degree = 0} :=
    ⟨⟨⟨0, by simp⟩⟩, fun s ↦ Subtype.ext ((Finsupp.degree_eq_zero_iff _).1 s.2)⟩
  exact ⟨e.toLinearEquiv ≪≫ₗ a ≪≫ₗ (homogeneousSubmoduleBasis N k 0).repr ≪≫ₗ
    Finsupp.uniqueLinearEquiv k k default⟩

/-- Serre's computation, including dimension zero, the canonical sheaf, and the
cohomology of the structure sheaf. All cohomology is computed in module sheaves, and
all displayed cohomology isomorphisms are in `ModuleCat k`.

Source: blueprint main-20261015, sec-picard-framework/sk-thm-picard-pn/_section.md;
Stacks Project, Tag 01XT, lemma-cohomology-projective-space-over-ring, equation-identify;
blueprint lem-pc-projective-space-canonical. (blueprint: sk-thm-picard-pn)

Proof:
1. Use the source library's twist cohomology computation, which implements the unit's
standard affine Cech cover, Laurent-monomial decomposition and exponent homology.
The realized decomposition and exponent-homology modules remain imported for that route.
2. The natural additive comparison between module-derived and abelian-sheaf cohomology
is k-linear: apply its naturality to scalar multiplication and use the scalar-endomorphism
formula on module cohomology. Transport the source's polynomial, vanishing and dual formulas.
3. With one homogeneous coordinate the sole chart is all of projective space and is
zero-dimensional affine space over the base. Its structure morphism is an isomorphism.
The twist generator on that chart trivializes every twist; the source's dimension-zero
cohomology formula supplies its sections, and the middle-degree formula gives vanishing.
4. Compare the sectionwise exterior sheaf with the source's exterior power and apply the
source's canonicalModuleIsoTwist, valid also in dimension zero.
5. Transport O(0) to the unit sheaf. The monomial basis in degree zero has exactly one
index, the zero exponent. Positive cohomology vanishes by the middle- or top-degree formula. -/
theorem picard_pn (k : Type u) [Field k] (n : ℕ) :
    (∀ m : ℤ, 0 ≤ m →
      Nonempty (
        (ModuleCat.restrictScalars
          (Scheme.globalSectionsRingHom k (X := ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))))).obj
          ((RingedSpace.moduleCohomology
            ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)).toRingedSpace 0).obj
            (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) m)) ≅
          ModuleCat.of k
            (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) k m.toNat))) ∧
    (∀ (q : ℕ) (m : ℤ), q ≠ 0 → q ≠ n →
      IsZero (
        (ModuleCat.restrictScalars
          (Scheme.globalSectionsRingHom k (X := ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))))).obj
          ((RingedSpace.moduleCohomology
            ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)).toRingedSpace q).obj
            (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) m)))) ∧
    (1 ≤ n → ∀ m : ℤ, -(n : ℤ) ≤ m →
      IsZero (
        (ModuleCat.restrictScalars
          (Scheme.globalSectionsRingHom k (X := ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))))).obj
          ((RingedSpace.moduleCohomology
            ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)).toRingedSpace n).obj
            (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) m)))) ∧
    (1 ≤ n → ∀ m : ℤ, m ≤ -(n : ℤ) - 1 →
      Nonempty (
        (ModuleCat.restrictScalars
          (Scheme.globalSectionsRingHom k (X := ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))))).obj
          ((RingedSpace.moduleCohomology
            ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)).toRingedSpace n).obj
            (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) m)) ≅
          ModuleCat.of k (Module.Dual k
            (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) k
              (-m - n - 1).toNat)))) ∧
    (n = 0 → IsIso (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)) ↘ Spec (.of k)) ∧
      ∀ m : ℤ,
        Nonempty (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) m ≅
          SheafOfModules.unit ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)).ringCatSheaf) ∧
        Nonempty (
          (ModuleCat.restrictScalars
            (Scheme.globalSectionsRingHom k (X := ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))))).obj
            ((RingedSpace.moduleCohomology
              ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)).toRingedSpace 0).obj
              (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) m)) ≅ ModuleCat.of k k) ∧
        ∀ q : ℕ, q ≠ 0 → IsZero (
          (ModuleCat.restrictScalars
            (Scheme.globalSectionsRingHom k (X := ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))))).obj
            ((RingedSpace.moduleCohomology
              ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)).toRingedSpace q).obj
              (twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) m)))) ∧
    Nonempty (Scheme.Modules.exteriorSheaf
      (ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)) ↘ Spec (.of k)).relativeDifferentials n ≅
        twist (ULift.{u} (Fin (n + 1))) (Spec (.of k)) (-(n : ℤ) - 1)) ∧
    Nonempty (
      (ModuleCat.restrictScalars
        (Scheme.globalSectionsRingHom k (X := ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))))).obj
        ((RingedSpace.moduleCohomology
          ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)).toRingedSpace 0).obj
          (SheafOfModules.unit ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)).ringCatSheaf)) ≅
        ModuleCat.of k k) ∧
    (∀ q : ℕ, q ≠ 0 → IsZero (
      (ModuleCat.restrictScalars
        (Scheme.globalSectionsRingHom k (X := ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k))))).obj
        ((RingedSpace.moduleCohomology
          ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)).toRingedSpace q).obj
          (SheafOfModules.unit ℙ(ULift.{u} (Fin (n + 1)); Spec (.of k)).ringCatSheaf)))) := by
  classical
  let N := ULift.{u} (Fin (n + 1))
  let X := ℙ(N; Spec (.of k))
  have hN : Nat.card N = n + 1 := by simp [N]
  have comp (F : X.Modules) (q : ℕ) := cohomology_linear_comparison k X F q
  have hz (q : ℕ) (m : ℤ) (h : Subsingleton ((twist N (Spec (.of k)) m).H q)) :
      IsZero ((ModuleCat.restrictScalars (Scheme.globalSectionsRingHom k (X := X))).obj
        ((RingedSpace.moduleCohomology X.toRingedSpace q).obj
          (twist N (Spec (.of k)) m))) := by
    obtain ⟨e⟩ := comp (twist N (Spec (.of k)) m) q
    exact ModuleCat.isZero_iff_subsingleton.mpr e.toEquiv.subsingleton
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm
    obtain ⟨e⟩ := comp (twist N (Spec (.of k)) m) 0
    obtain ⟨a⟩ := nonempty_H_zero_twist_equiv N k n hN m.toNat
    have he : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm
    rw [he] at a
    exact ⟨(e ≪≫ₗ a).toModuleIso⟩
  · intro q m hq0 hqn
    exact hz q m (subsingleton_H_twist_of_ne N k n hN q m hq0 hqn)
  · intro hn m hm
    exact hz n m (subsingleton_H_twist_top N k n (by omega) hN m hm)
  · intro _ m hm
    obtain ⟨e⟩ := comp (twist N (Spec (.of k)) m) n
    obtain ⟨a⟩ := nonempty_H_twist_top_equiv_dual N k n hN m hm
    exact ⟨(e ≪≫ₗ a).toModuleIso⟩
  · intro hn
    subst n
    refine ⟨zero_dim_isIso _, fun m ↦ ⟨zero_dim_twist _ m, ?_, ?_⟩⟩
    · obtain ⟨e⟩ := cohomology_linear_comparison k _
        (twist (ULift.{u} (Fin 1)) (Spec (.of k)) m) 0
      obtain ⟨a⟩ := nonempty_H_zero_twist_linearEquiv_of_card_eq_one
        (n := ULift.{u} (Fin 1)) k (by simp) m
      exact ⟨(e ≪≫ₗ a).toModuleIso⟩
    · intro q hq
      exact hz q m (subsingleton_H_twist_of_ne _ k 0 hN q m hq hq)
  · exact ⟨exteriorSheafIsoExteriorPower (X ↘ Spec (.of k)).relativeDifferentials n ≪≫
      canonicalModuleIsoTwist k (Equiv.ulift.trans (Equiv.refl _))⟩
  · obtain ⟨e⟩ := comp (SheafOfModules.unit X.ringCatSheaf) 0
    obtain ⟨a⟩ := structure_H_zero k n
    exact ⟨(e ≪≫ₗ a).toModuleIso⟩
  · intro q hq
    have h : Subsingleton ((twist N (Spec (.of k)) 0).H q) := by
      by_cases hqn : q = n
      · subst q
        exact subsingleton_H_twist_top N k n hq hN 0 (by omega)
      · exact subsingleton_H_twist_of_ne N k n hN q 0 hq hqn
    have : Subsingleton ((Scheme.Modules.unit X).H q) :=
      subsingleton_H_of_iso (unitIsoTwistZero N (Spec (.of k))).symm q
    obtain ⟨e⟩ := comp (SheafOfModules.unit X.ringCatSheaf) q
    exact ModuleCat.isZero_iff_subsingleton.mpr e.toEquiv.subsingleton

end AlgebraicGeometry.ProjectiveSpace
