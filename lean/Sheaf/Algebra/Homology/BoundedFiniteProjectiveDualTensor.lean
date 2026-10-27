/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import WeilConjectures.Algebra.Homology.ModuleHomComplex
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Data.Int.Interval

/-! # Bounded finite-projective dual and tensor complexes

Source: Stacks Project, More on Algebra, Tag 07VI, and Algebra, Tag 00NX.
(blueprint: lem-pod-bounded-finite-projective-dual-tensor).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

namespace CochainComplex

variable {R : Type u} [CommRing R]

private def dualDegreeIso (P : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    (moduleHomComplex P ((singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R R))).X n ≅ ModuleCat.of R (Module.Dual R (P.X (-n))) := by
  let e : HomComplex.Cochain P
      ((singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) n ≃ₗ[R]
        (P.X (-n) ⟶ ModuleCat.of R R) :=
    { HomComplex.Cochain.toSingleEquiv (neg_add_cancel n) with
      map_smul' := by
        intro r z
        simp [HomComplex.Cochain.toSingleEquiv] }
  exact (e.trans ModuleCat.homLinearEquiv).toModuleIso

private def tensorDegreeIso
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ) (a b n : ℤ)
    (hP : ∀ p, p < a ∨ b < p → IsZero (P.X p)) :
    (∐ fun p : ↥(Finset.Icc a b) ↦ P.X p ⊗ Q.X (n - p)) ≅
      (mapBifunctor P Q (curriedTensor _)).X n := by
  classical
  let F := fun p : ↥(Finset.Icc a b) ↦ P.X p ⊗ Q.X (n - p)
  let f : ∐ F ⟶ (mapBifunctor P Q (curriedTensor _)).X n :=
    Sigma.desc (fun p ↦ ιMapBifunctor P Q (curriedTensor _) p (n - p) n (by simp))
  let g : (mapBifunctor P Q (curriedTensor _)).X n ⟶ ∐ F :=
    HomologicalComplex.mapBifunctorDesc (fun p q hpq ↦
      if h : p ∈ Finset.Icc a b then
        eqToHom (congrArg (fun j ↦ P.X p ⊗ Q.X j) (show q = n - p by
          change p + q = n at hpq
          omega)) ≫ Sigma.ι F ⟨p, h⟩
      else 0)
  refine ⟨f, g, ?_, ?_⟩
  · apply Sigma.hom_ext
    intro p
    dsimp only [f, g]
    rw [← Category.assoc, Sigma.ι_desc, HomologicalComplex.ι_mapBifunctorDesc]
    simp only [dif_pos p.property, eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    change p + q = n at hpq
    by_cases hp : p ∈ Finset.Icc a b
    · have hq : q = n - p := by omega
      subst q
      dsimp only [f, g]
      rw [← Category.assoc, HomologicalComplex.ι_mapBifunctorDesc]
      simp only [dif_pos hp, eqToHom_refl, Category.id_comp, Sigma.ι_desc,
        Category.comp_id]
    · have hz : IsZero (P.X p ⊗ Q.X q) :=
        (tensorRight (Q.X q)).map_isZero (hP p (by simp only [Finset.mem_Icc] at hp; omega))
      exact hz.eq_of_src _ _

/-- The ordinary product Hom dual and the signed total tensor of a bounded
finite-projective complex are bounded and termwise finite projective.
Source: Stacks Project, More on Algebra, Tag 07VI, and Algebra, Tag 00NX.
(blueprint: lem-pod-bounded-finite-projective-dual-tensor).

Proof: project a Hom cochain onto its unique potentially nonzero component in
bidegree (-n,0). This identifies the dual term with the module dual of P^(-n),
so finite projectivity is preserved and the support reverses. In tensor degree n,
discard the zero summands with first index outside [a,b]. The remaining finite
coproduct has finite-projective tensor factors, hence is finite projective.
A summand in a degree outside [a-b,b-a] has a zero factor. The coproduct
universal property then shows that the total term is zero. The argument also
covers a>b: all original terms and all summands are zero. -/
theorem bounded_finiteProjective_dual_tensor
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (ha : P.IsStrictlyGE a) (hb : P.IsStrictlyLE b)
    (hP : ∀ i, Module.Projective R (P.X i) ∧ Module.Finite R (P.X i)) :
    let D := moduleHomComplex P ((singleFunctor (ModuleCat.{u} R) 0).obj
      (ModuleCat.of R R))
    ∀ Q ∈ [D, mapBifunctor P D (curriedTensor _)],
      (∃ c d : ℤ, Q.IsStrictlyGE c ∧ Q.IsStrictlyLE d) ∧
      ∀ i, Module.Projective R (Q.X i) ∧ Module.Finite R (Q.X i) := by
  let D := moduleHomComplex P ((singleFunctor (ModuleCat.{u} R) 0).obj
    (ModuleCat.of R R))
  have hzero (i : ℤ) (hi : i < a ∨ b < i) : IsZero (P.X i) := by
    rcases hi with hi | hi
    · exact P.isZero_of_isStrictlyGE a i hi
    · exact P.isZero_of_isStrictlyLE b i hi
  have hDzero (i : ℤ) (hi : i < -b ∨ -a < i) : IsZero (D.X i) := by
    have hz := hzero (-i) (by omega)
    have hsub : Subsingleton (P.X (-i)) := ModuleCat.isZero_iff_subsingleton.mp hz
    let _ := hsub
    exact ModuleCat.isZero_iff_subsingleton.mpr
      (Equiv.subsingleton (dualDegreeIso P i).toLinearEquiv.toEquiv)
  have hD (i : ℤ) : Module.Projective R (D.X i) ∧ Module.Finite R (D.X i) := by
    have := (hP (-i)).1
    have := (hP (-i)).2
    exact ⟨Module.Projective.of_equiv (dualDegreeIso P i).toLinearEquiv.symm,
      Module.Finite.equiv (dualDegreeIso P i).toLinearEquiv.symm⟩
  have hDb : D.IsStrictlyGE (-b) ∧ D.IsStrictlyLE (-a) :=
    ⟨(D.isStrictlyGE_iff _).mpr (fun i hi ↦ hDzero i (Or.inl hi)),
      (D.isStrictlyLE_iff _).mpr (fun i hi ↦ hDzero i (Or.inr hi))⟩
  let T := mapBifunctor P D (curriedTensor _)
  have hTzero (i : ℤ) (hi : i < a - b ∨ b - a < i) : IsZero (T.X i) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    change p + q = i at hpq
    have hz : IsZero (P.X p ⊗ D.X q) := by
      by_cases hp : p < a ∨ b < p
      · exact (tensorRight (D.X q)).map_isZero (hzero p hp)
      · exact (tensorLeft (P.X p)).map_isZero (hDzero q (by omega))
    exact hz.eq_of_src _ _
  have hT (i : ℤ) : Module.Projective R (T.X i) ∧ Module.Finite R (T.X i) := by
    have (p : ℤ) := (hP p).1
    have (p : ℤ) := (hP p).2
    have (q : ℤ) := (hD q).1
    have (q : ℤ) := (hD q).2
    let F := fun p : ↥(Finset.Icc a b) ↦ P.X p ⊗ D.X (i - p)
    let e := (ModuleCat.coprodIsoDirectSum F).symm ≪≫ tensorDegreeIso P D a b i hzero
    have (p : ↥(Finset.Icc a b)) : Module.Projective R (F p) := by
      change Module.Projective R (P.X p ⊗[R] D.X (i - p))
      infer_instance
    have (p : ↥(Finset.Icc a b)) : Module.Finite R (F p) := by
      change Module.Finite R (P.X p ⊗[R] D.X (i - p))
      infer_instance
    have : Module.Finite R (DirectSum ↥(Finset.Icc a b) (fun p ↦ F p)) :=
      Module.Finite.equiv (DirectSum.linearEquivFunOnFintype R _ _).symm
    exact ⟨Module.Projective.of_equiv e.toLinearEquiv,
      Module.Finite.equiv e.toLinearEquiv⟩
  dsimp only
  intro Q hQ
  change Q ∈ [D, T] at hQ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hQ
  rcases hQ with rfl | rfl
  · exact ⟨⟨-b, -a, hDb⟩, hD⟩
  · exact ⟨⟨a - b, b - a,
      (T.isStrictlyGE_iff _).mpr (fun i hi ↦ hTzero i (Or.inl hi)),
      (T.isStrictlyLE_iff _).mpr (fun i hi ↦ hTzero i (Or.inr hi))⟩, hT⟩

end CochainComplex
