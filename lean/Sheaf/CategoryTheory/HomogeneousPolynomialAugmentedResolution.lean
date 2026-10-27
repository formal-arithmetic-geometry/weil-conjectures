/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q116
-/
module

public import Sheaf.CategoryTheory.ContinuousScalarRing
public import Sheaf.Topology.LadicLattice
public import Sheaf.CategoryTheory.CondensedDerivedRestrictionCalculus
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Flat.TorsionFree

public import Sheaf.CategoryTheory.HomogeneousPolynomialResolutionData
import Sheaf.CategoryTheory.HomogeneousPolynomialModelExistence
import Sheaf.CategoryTheory.HomogeneousPolynomialContractionExistence
import Sheaf.CategoryTheory.CondensedDerivedInvariants
import Mathlib.Algebra.Homology.SingleHomology

/-! # The augmented homogeneous polynomial resolution

Source: current blueprint, six-functors direct-images proof, paragraph (3),
agent-formulated homogeneous polynomial reduction, construction and inserted-zero contraction
(blueprint: lem-sfb-homogeneous-polynomial-augmented-resolution).
The blueprint delegates this input; an exact literature reference is WANTED.

Coproduct presentations and formulas on all generalized monomial sections specify the
complex and augmentation. Existence is asserted without choosing unspecified data.
The contraction is in internal modules after forgetting actions.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.CondensedBar
open Profinite.CondensedAction (continuousScalarRing)

namespace Profinite.CondensedAction.HomogeneousPolynomial

private theorem exact_of_contraction {C : Type*} [Category* C] [Abelian C]
    (S : ShortComplex C) (r : S.X₂ ⟶ S.X₁) (s : S.X₃ ⟶ S.X₂)
    (h : r ≫ S.f + S.g ≫ s = 𝟙 _) : S.Exact := by
  rw [S.exact_iff_kernel_ι_comp_cokernel_π_zero]
  calc
    kernel.ι S.g ≫ cokernel.π S.f =
        kernel.ι S.g ≫ (r ≫ S.f + S.g ≫ s) ≫ cokernel.π S.f := by
      rw [h, Category.id_comp]
    _ = 0 := by
      simp [Preadditive.add_comp, Category.assoc,
        ← Category.assoc (kernel.ι S.g) S.g]

private theorem augmentation_quasiIso (ell : ℕ) [Fact ell.Prime]
    (F : Type u) [NormedField F] [NormedAlgebra ℚ_[ell] F] (r : ℕ)
    (P : Model ell F r) (h : Contraction ell F r P) : QuasiIso P.augmentation := by
  let A := continuousScalarRing F
  let G := Profinite.LadicLattice.Lattice.{u} ell r
  let U : CategoryTheory.CondensedBar.Equivariant A G ⥤
      CategoryTheory.CondensedBar.Modules A := CategoryTheory.CondensedBar.forgetAction
  have : U.Faithful := ⟨fun h ↦ Subtype.ext h⟩
  have he (S : ShortComplex (CategoryTheory.CondensedBar.Equivariant A G)) :
      S.Exact ↔ (S.map U).Exact :=
    (CategoryTheory.CondensedDerivedRestriction.forgetExact A G).2.2 S
  rw [quasiIso_iff]
  intro i
  by_cases hi : i = 0
  · subst i
    rw [quasiIsoAt_iff' _ (-1) 0 1 (by simp) (by simp)]
    rw [ShortComplex.quasiIso_iff_of_zeros _ (by simp) (by simp)
      (P.negative (-1) (by omega) |>.eq_of_src _ _)]
    let e := HomologicalComplex.singleObjXSelf (.up ℤ) 0
      ((trivial (R := A.toMon) (P := G)).obj (Mod.regular A.X))
    have ha : e.inv.val ≫ (P.augmentation.f 0).val = P.ι 0 0 :=
      P.augmentation_zero
    constructor
    · apply (he _).2
      apply exact_of_contraction _ (h.h0 ≫ e.inv.val) (h.h 0)
      change (h.h0 ≫ e.inv.val) ≫ (P.augmentation.f 0).val +
        (P.cochain.d 0 1).val ≫ h.h 0 = 𝟙 _
      simpa only [Category.assoc, ha] using h.zero_identity
    · apply U.mono_of_mono_map
      change Mono (P.augmentation.f 0).val
      have ha' : (P.augmentation.f 0).val = e.hom.val ≫ P.ι 0 0 := by
        rw [← ha]
        change _ = U.map e.hom ≫ U.map e.inv ≫ _
        simp
      have hs : (P.augmentation.f 0).val ≫ (h.h0 ≫ e.inv.val) = 𝟙 _ := by
        rw [ha', ← Category.assoc, Category.assoc e.hom.val, h.split]
        change U.map e.hom ≫ 𝟙 _ ≫ U.map e.inv = 𝟙 _
        simp [← U.map_comp]
      exact (show SplitMono (P.augmentation.f 0).val from ⟨h.h0 ≫ e.inv.val, hs⟩).mono
  · apply (quasiIsoAt_iff_exactAt _ i
      (HomologicalComplex.exactAt_single_obj (.up ℤ) 0 _ i hi)).2
    by_cases hn : i < 0
    · exact HomologicalComplex.ExactAt.of_isZero (P.negative i hn)
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = (n + 1 : ℕ) := by
        refine ⟨(i - 1).toNat, ?_⟩
        omega
      rw [HomologicalComplex.exactAt_iff' _ (n : ℤ) ((n + 1 : ℕ) : ℤ)
        ((n + 2 : ℕ) : ℤ) (by simp) (by simp; omega)]
      apply (he _).2
      exact exact_of_contraction _ (h.h n) (h.h (n + 1)) (h.positive_identity n)

/-- The homogeneous polynomial augmented resolution and its inserted-zero contraction,
for both the finite intermediate field and the noncomplete norm-topological algebraic closure.
Source: current blueprint, direct-images proof paragraph (3), delegated polynomial input
(blueprint: lem-sfb-homogeneous-polynomial-augmented-resolution).

Proof:
1. Coefficientwise restriction makes the finite polynomial modules sheaves: finite disjoint
   unions have finite unions of supports; along a profinite surjection descend the finitely
   many coefficients using def-sfb-continuous-map-condensed-ring and the coherent sheaf
   criterion lem-sfb-profinite-coherent-sheaf-criterion. The empty parameter gives zero.
   The internal/sectionwise equivalence def-weil-pbc-internal-abelian-sheaf-module-equivalence
   identifies this with the monomial coproduct, using sk-def-sfb-sheaf-tensor.
2. Polynomial substitution defines deletion, zero insertion and diagonal translation over
   C(S,F). It fixes coefficients and commutes with restriction. On generators translation
   by g followed by t is translation by g+t, and zero acts identically. This is precisely
   the action in def-sfb-condensed-action-module for def-sfb-ladic-lattice.
3. Double deletions cancel in pairs, with signs (-1)^(a+b-1) and (-1)^(a+b). Translation
   commutes with every deletion. Constants are fixed, and delta^0 kills constants, giving
   the augmented equivariant complex with d squared zero.
4. Evaluate at zero: h^0 a=1 and h^1 delta^0 f=f-f(0), proving the degree-zero identity.
5. In positive degrees expand the two composites. The leading term is f; every other
   omitted-block term with inserted zero occurs twice with opposite signs. This proves
   the displayed positive contraction identity internally and naturally in parameters.
6. The contraction identifies degree-zero cycles with A and makes positive cycles
   boundaries. Negative degrees vanish, so the underlying augmentation is a quasi-isomorphism.
7. The forgetting functor creates kernels and cokernels and detects exactness by
   lem-sfb-condensed-derived-restriction-calculus. Thus the augmentation is an equivariant
   quasi-isomorphism; def-weil-abstract-derived-category inverts it in the ordinary D.
8. For r=0 there is only the constant monomial, each h is identity, and delta alternates
   between zero and identity. Every construction is a finite polynomial calculation;
   neither coefficient field is completed and all continuous coefficient maps are retained.
-/
theorem homogeneous_polynomial_augmented_resolution (ell : ℕ) [Fact ell.Prime]
    (Ω : Type u) [NormedField Ω] [NormedAlgebra ℚ_[ell] Ω] [IsAlgClosure ℚ_[ell] Ω]
    (E : IntermediateField ℚ_[ell] Ω) [FiniteDimensional ℚ_[ell] E] (r : ℕ) :
    Assertion ell E r ∧ Assertion ell Ω r := by
  have assertion (F : Type u) [NormedField F] [NormedAlgebra ℚ_[ell] F] :
      Assertion ell F r := by
    refine ⟨model_nonempty ell F r, fun P ↦ ?_⟩
    obtain ⟨h⟩ := contraction_nonempty ell F r P
    have := augmentation_quasiIso ell F r P h
    exact ⟨⟨h⟩, inferInstance, inferInstance⟩
  exact ⟨assertion E, assertion Ω⟩

end Profinite.CondensedAction.HomogeneousPolynomial
