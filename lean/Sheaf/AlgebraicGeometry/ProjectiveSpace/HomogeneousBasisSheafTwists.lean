/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Sheaf.AlgebraicGeometry.ProjGradedModuleSheafExists
public import Sheaf.AlgebraicGeometry.ProjectiveLineProjChartIsomorphism
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist

import Sheaf.AlgebraicGeometry.ProjShiftedFreeTwist
import Sheaf.AlgebraicGeometry.ProjTildeFunctorial
import Sheaf.AlgebraicGeometry.ProjectiveLineTwistExists
import Sheaf.AlgebraicGeometry.TensorPullback
import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules

/-!
# Homogeneous bases give finite sums of twists

Source: blueprint `lem-sc-p1-graded-resolution`, shifted-free clause;
Stacks Project, Constructions, Definitions 01M6, 01MN and Lemma 01M7.
(blueprint: lem-sc-p1-homogeneous-basis-sheaf-twists).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite TopologicalSpace LocalizedModule HomogeneousLocalization
open MvPolynomial

namespace AlgebraicGeometry.Proj

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The inverse transport of an associated sheaf of a finite graded free module is the
finite sum of twists with the prescribed basis degrees. No resolution or exactness is assumed.
Source: blueprint `lem-sc-p1-graded-resolution`, shifted-free clause;
Stacks Project, Constructions, Definitions 01M6, 01MN and Lemma 01M7.
(blueprint: lem-sc-p1-homogeneous-basis-sheaf-twists).

Proof:
1. The basis coordinate equivalence identifies `M` with `Fin r → k[x₀,x₁]`.
   Decompose each polynomial coefficient into homogeneous parts. Because `b a` has
   degree `-d a`, the term with coefficient of degree n has degree `n - d a`.
   Internality of the grading implies that the degree-j component is exactly the
   tuples whose a-th coefficient has degree `d a + j`, or is zero if that degree
   is negative. Thus this is a degree-preserving isomorphism with `⊕ S(d a)`.
2. By `lem-sc-p1-proj-shifted-free-twist`, the finite coproduct of the Proj twists has
   exactly the associated-sheaf charts for this sum. The coordinate equivalence of
   step 1 induces an isomorphism of associated sheaves by
   `lem-sc-p1-proj-tilde-functorial`; the supplied chart maps identify its domain with `F`.
3. Pull back this isomorphism along `C.iso.inv`. Pullback by an isomorphism is an
   equivalence (composition and identity comparisons), hence commutes with coproducts.
   For each d, on the two standard charts, the generator of `S(d)` is `xᵢᵈ` and
   the two generators satisfy `x₀ᵈ = t⁻ᵈ x₁ᵈ`. The chart equations of `C` therefore
   identify the transported Proj twist with `ProjectiveSpace.twist d`, by gluing
   the two rank-one trivializations. The tensor-formula pullback of the shifted-free
   lemma agrees with `Scheme.Modules.pullback` by uniqueness of left adjoints to the
   same pushforward. Taking the coproduct gives the required isomorphism. For r = 0
   the basis forces `M = 0`, and both associated sheaf and empty coproduct are zero. -/
theorem homogeneous_basis_sheaf_twists (k : Type u) [Field k]
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
    (r : ℕ) (d : Fin r → ℤ)
    (b : Module.Basis (Fin r) (MvPolynomial (Fin 2) k) M)
    (hb : ∀ a : Fin r, b a ∈ 𝓜 (-(d a))) :
    Nonempty ((Scheme.Modules.pullback C.iso.inv).obj F ≅
      ∐ (fun a ↦ ProjectiveSpace.twist (ULift.{u} (Fin 2)) (Spec (.of k)) (d a))) := by
  sorry

end AlgebraicGeometry.Proj
