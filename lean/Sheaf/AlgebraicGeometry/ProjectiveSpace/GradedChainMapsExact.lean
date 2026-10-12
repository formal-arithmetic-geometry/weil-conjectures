/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Sheaf.Algebra.Module.DegreeZeroFractions
public import Sheaf.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

import Sheaf.AlgebraicGeometry.ProjGradedModuleSheafExists

import Sheaf.AlgebraicGeometry.ProjSheafificationExact
import Sheaf.AlgebraicGeometry.ProjTildeFunctorial
import Sheaf.AlgebraicGeometry.ProjStandardOpenProperties
import Sheaf.Topology.SheafOfModulesFromBasis

/-!
# Exact maps on fixed associated graded-module sheaves

Source: Stacks Project, Tag 01M7, final paragraph.
(blueprint: lem-sc-p1-graded-chain-maps-exact).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace LocalizedModule HomogeneousLocalization
open MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Fixed associated sheaves of an exact graded chain admit an exact chain of maps.
Source: Stacks Project, Constructions, Tag 01M7, final paragraph.
(blueprint: lem-sc-p1-graded-chain-maps-exact).

Proof:
1. Give K = range f₁ its induced grading. Degree-preserving maps have graded images
   and kernels: decompose preimages into their homogeneous components and compare
   components using internality. The given range/kernel equalities split the chain
   into the short exact sequences A₂ → A₁ → K and K → A₀ → M.
2. Use the underlying additive-subgroup polynomial grading when applying
   gradedModuleSheaf_exists and tilde_functorial. Identify its Proj with the
   homogeneous-submodule Proj by identical homogeneous ideals and fractions; the
   chart ring maps and restrictions agree under this identification. Construct the
   associated sheaf of K using gradedModuleSheaf_exists. For the fixed
   sheaves Eᵢ and F, the injective chart maps identify their sections with the same
   degree-zero fractions as the canonical associated sheaves. The restriction and
   scalar formulas give unique isomorphisms on the standard-open basis, so transport
   the canonical stalk charts across these isomorphisms.
3. Apply tilde_functorial to the two triples to obtain maps with the chart fraction
   formulas. Apply proj_sheafification_shortExact to both short exact sequences.
4. Compose the map E₁ → K~ with K~ → E₀. The first short exact sequence gives a
   monic E₂ → E₁, the second an epic E₀ → F. At E₁, composing with a mono does not
   change the kernel; at E₀, composing with an epi does not change the image.
   Consequently the spliced chain is exact at both middle terms. -/
theorem graded_chain_maps_exact (k : Type u) [Field k]
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
    (hex₀ : LinearMap.range f₁ = LinearMap.ker f₀) (hsurj : Function.Surjective f₀)
    (E : Fin 3 → (Proj (homogeneousSubmodule (Fin 2) k)).Modules)
    (hE : (∀ i : Fin 3,
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
                mk (a ^ m • y) (⟨g ^ (e * m), ⟨e * m, rfl⟩⟩ : Submonoid.powers g)))) :
    ∃ (g₂ : E 2 ⟶ E 1) (g₁ : E 1 ⟶ E 0) (g₀ : E 0 ⟶ F),
      Mono g₂ ∧ Epi g₀ ∧ (ComposableArrows.mk₃ g₂ g₁ g₀).Exact := by
  sorry

end AlgebraicGeometry.Proj
