/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Mathlib.Algebra.Homology.ExactSequence
public import Sheaf.AlgebraicGeometry.ProjGradedModuleSheafExists
public import Sheaf.AlgebraicGeometry.ProjectiveLineProjChartIsomorphism

import Sheaf.AlgebraicGeometry.ProjSheafificationExact
import Sheaf.AlgebraicGeometry.ProjTildeFunctorial
import Sheaf.AlgebraicGeometry.TensorPullback

/-!
# Exactness of an associated graded chain on the projective line

Source: blueprint `lem-sc-p1-graded-resolution`, sheafification clause;
Stacks Project, Constructions, Tag 01M7, final paragraph.
(blueprint: lem-sc-p1-sheafify-graded-chain).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace LocalizedModule HomogeneousLocalization
open MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Sheafification and inverse transport of a given exact graded chain. The terms need not
be free or finitely generated; the conclusion supplies their associated sheaf chart data.
Source: blueprint `lem-sc-p1-graded-resolution`, sheafification clause;
Stacks Project, Constructions, Tag 01M7, final paragraph.
(blueprint: lem-sc-p1-sheafify-graded-chain).

Proof:
1. Form the graded image `K = range f₁`, with its grading induced from `A 0`. A
   degree-preserving map has a graded image: decompose a preimage into homogeneous parts
   and use internality in its source and target. Similarly its kernel is graded.
   The supplied range/kernel equalities give the short exact sequences
   `0 → A 2 → A 1 → K → 0` and `0 → K → A 0 → M → 0`.
2. Apply `lem-weil-pbc-proj-graded-module-sheaf-exists` to the three `A i` and to `K`.
   Retain its injective chart maps onto the degree-zero fractions, scalar compatibility,
   and restriction formulas as the displayed chart data for the three resulting sheaves.
   Use the supplied chart data for `F` as the associated sheaf of `M`.
3. `lem-sc-p1-proj-tilde-functorial` induces the maps, including the maps to and from
   the sheaf of `K`. The composition formula identifies the middle map with the
   composite through `K`. Apply `lem-sc-p1-proj-sheafification-exact` to the two short
   exact sequences and splice them. Thus the first map is monic, the last is epic,
   and the chain is exact at its two middle terms.
4. Module pullback along the inverse of `C.iso` is an equivalence: its inverse is
   pullback along `C.iso.hom`, and the composition and identity isomorphisms give the
   two inverse comparisons. Equivalences preserve kernels and cokernels, so preserve
   monomorphisms, epimorphisms and exactness. Apply this pullback to the chain of step 3.
   The output chart data remain on Proj; only the displayed arrows are transported. -/
theorem sheafify_graded_chain (k : Type u) [Field k]
    (C : ProjectiveLine.ProjChartIsomorphism k)
    (M : ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (𝓜 : ℤ → AddSubgroup M) (h𝓜 : DirectSum.IsInternal 𝓜)
    (hsmul : ∀ (n : ℕ) (z : ℤ) (a : MvPolynomial (Fin 2) k) (y : M),
      a ∈ homogeneousSubmodule (Fin 2) k n → y ∈ 𝓜 z → a • y ∈ 𝓜 (n + z))
    (F : (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    (alpha : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ),
      0 < d → f ∈ homogeneousSubmodule (Fin 2) k d →
      F.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
        LocalizedModule.Away f M)
    (halpha : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d),
        Function.Injective (alpha f d hd hf) ∧
        Set.range (alpha f d hd hf) = degreeZeroFractions
          (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
          (fun n : ℕ ↦ (𝓜 n : Set M)) (Submonoid.powers f))
    (hscalar : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
        (r : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
        (s : F.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
        alpha f d hd hf (awayToSection (homogeneousSubmodule (Fin 2) k) f r • s) =
          algebraMap (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
            (Localization.Away f) r • alpha f d hd hf s)
    (hres : ∀ (f g : MvPolynomial (Fin 2) k) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
        (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
        (hg : g ∈ homogeneousSubmodule (Fin 2) k b)
        (inc : basicOpen (homogeneousSubmodule (Fin 2) k) g ≤
          basicOpen (homogeneousSubmodule (Fin 2) k) f)
        (e c : ℕ) (a : MvPolynomial (Fin 2) k),
        0 < e → a ∈ homogeneousSubmodule (Fin 2) k c → g ^ e = a * f →
        ∀ (m : ℕ) (y : M)
          (s : F.val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
          alpha f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
          alpha g b hb hg (F.val.map (homOfLE inc).op s) =
            mk (a ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g))
    (A : Fin 3 → ModuleCat.{u} (MvPolynomial (Fin 2) k))
    (𝒢 : ∀ i : Fin 3, ℤ → AddSubgroup (A i))
    (f₂ : A 2 →ₗ[MvPolynomial (Fin 2) k] A 1)
    (f₁ : A 1 →ₗ[MvPolynomial (Fin 2) k] A 0)
    (f₀ : A 0 →ₗ[MvPolynomial (Fin 2) k] M)
    (h𝒢 : ∀ i : Fin 3, DirectSum.IsInternal (𝒢 i))
    (hA_smul : ∀ (i : Fin 3) (n : ℕ) (j : ℤ) (s : MvPolynomial (Fin 2) k) (x : A i),
        s ∈ homogeneousSubmodule (Fin 2) k n → x ∈ 𝒢 i j →
          s • x ∈ 𝒢 i ((n : ℤ) + j))
    (hf₂ : ∀ (j : ℤ) (x : A 2), x ∈ 𝒢 2 j → f₂ x ∈ 𝒢 1 j)
    (hf₁ : ∀ (j : ℤ) (x : A 1), x ∈ 𝒢 1 j → f₁ x ∈ 𝒢 0 j)
    (hf₀ : ∀ (j : ℤ) (x : A 0), x ∈ 𝒢 0 j → f₀ x ∈ 𝓜 j)
    (hinj : Function.Injective f₂) (hex₁ : LinearMap.range f₂ = LinearMap.ker f₁)
    (hex₀ : LinearMap.range f₁ = LinearMap.ker f₀) (hsurj : Function.Surjective f₀) :
    ∃ (E : Fin 3 → (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
      (g₂ : (Scheme.Modules.pullback C.iso.inv).obj (E 2) ⟶
        (Scheme.Modules.pullback C.iso.inv).obj (E 1))
      (g₁ : (Scheme.Modules.pullback C.iso.inv).obj (E 1) ⟶
        (Scheme.Modules.pullback C.iso.inv).obj (E 0))
      (g₀ : (Scheme.Modules.pullback C.iso.inv).obj (E 0) ⟶
        (Scheme.Modules.pullback C.iso.inv).obj F),
      (∀ i : Fin 3,
        ∃ (alpha : ∀ (f : MvPolynomial (Fin 2) k) (d : ℕ),
          0 < d → f ∈ homogeneousSubmodule (Fin 2) k d →
          (E i).val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f)) →+
            LocalizedModule.Away f (A i)),
          (∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
            (hf : f ∈ homogeneousSubmodule (Fin 2) k d),
            Function.Injective (alpha f d hd hf) ∧
            Set.range (alpha f d hd hf) = degreeZeroFractions
              (fun n : ℕ ↦ (homogeneousSubmodule (Fin 2) k n : Set (MvPolynomial (Fin 2) k)))
              (fun n : ℕ ↦ (𝒢 i n : Set (A i))) (Submonoid.powers f)) ∧
          (∀ (f : MvPolynomial (Fin 2) k) (d : ℕ) (hd : 0 < d)
            (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
            (r : HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
            (s : (E i).val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
            alpha f d hd hf (awayToSection (homogeneousSubmodule (Fin 2) k) f r • s) =
              algebraMap (HomogeneousLocalization.Away (homogeneousSubmodule (Fin 2) k) f)
                (Localization.Away f) r • alpha f d hd hf s) ∧
          (∀ (f g : MvPolynomial (Fin 2) k) (d b : ℕ) (hd : 0 < d) (hb : 0 < b)
            (hf : f ∈ homogeneousSubmodule (Fin 2) k d)
            (hg : g ∈ homogeneousSubmodule (Fin 2) k b)
            (inc : basicOpen (homogeneousSubmodule (Fin 2) k) g ≤
              basicOpen (homogeneousSubmodule (Fin 2) k) f)
            (e c : ℕ) (a : MvPolynomial (Fin 2) k),
            0 < e → a ∈ homogeneousSubmodule (Fin 2) k c → g ^ e = a * f →
            ∀ (m : ℕ) (y : A i)
              (s : (E i).val.obj (op (basicOpen (homogeneousSubmodule (Fin 2) k) f))),
              alpha f d hd hf s = mk y (⟨f ^ m, ⟨m, rfl⟩⟩ : Submonoid.powers f) →
              alpha g b hb hg ((E i).val.map (homOfLE inc).op s) =
                mk (a ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g))) ∧
      Mono g₂ ∧ Epi g₀ ∧ (ComposableArrows.mk₃ g₂ g₁ g₀).Exact := by
  sorry

end AlgebraicGeometry.Proj
