/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NI
-/
module

public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! # Reconstruction from a rank-one corner

Source: main-20261015 blueprint, sec-six-functors-basics,
sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3), agent coefficient auxiliary
(blueprint: lem-sfb-countable-endomorphism-module-reconstruction).

The basis is algebraic. The index type is countable and pointed, equivalently a nonempty
finite set or a copy of the natural numbers, with the distinguished index labelled zero.
The corner is the range of the rank-one operator's action on the algebraic module.
-/

@[expose] public section

set_option autoImplicit false

universe u v w t
open scoped TensorProduct

namespace Padic

/-- Countably spanned algebraic representations of the continuous endomorphism algebra
are reconstructed by the specified rank-one corner map.

Source: main-20261015 blueprint, sec-six-functors-basics,
sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3), agent coefficient auxiliary
(blueprint: lem-sfb-countable-endomorphism-module-reconstruction).

Proof:
1. The lower norm bound bounds every coordinate by the norm divided by c. Thus the
   coordinates and all matrix units E_ij are continuous; the latter have bound C/c.
   The same estimate makes theta_v(w) = lambda(w) v continuous.
2. The image eH is an E-subspace, and e acts identically there. The displayed formula
   is bilinear and T theta_v = theta_(Tv), so the tensor map intertwines the D-actions.
3. Expand a tensor as a finite sum of b_j tensor h_j. Applying E_0k to a relation
   between its images isolates h_k. This proves injectivity.
4. Its image N is a D-submodule. The quotient Q = H/N is countably spanned, and eQ = 0
   because eh = theta_(b_0)(eh). All finite coordinate projections therefore kill Q.
   For a finite basis their sum is the identity, so Q = 0.
5. For a countably infinite basis use lem-sfb-uncountable-almost-disjoint-family to
   obtain uncountably many infinite subsets A_i with finite pairwise intersections.
   Each A_i has an increasing bijective enumeration by the natural numbers.
6. Reindexing coordinates gives operators u_i and r_i, bounded by C/c, with
   r_i u_i = 1 and u_i r_i = p_i, the coordinate projection onto A_i.
7. For i distinct from j, p_i p_j is a finite coordinate projection and kills Q.
8. If q is nonzero in Q, the vectors u_i q are nonzero and linearly independent:
   applying p_i to a finite relation isolates its ith coefficient.
9. By lem-sfb-independent-family-spanning-cardinality (linearIndependent_le_span''),
   that independent index set injects into a countable spanning set of Q, impossible.
10. Hence Q = 0, so the tensor map is bijective; its inverse also intertwines D.
    This argument includes the zero module and a one-element basis.

The pure-tensor intertwining equation expresses D-linearity with D acting only on the
first tensor factor. The E-action on H is the scalar restriction of its unital D-action,
encoded by IsScalarTower; no topology on H is requested. -/
theorem countableEndomorphismModule_reconstruction
    (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (_hE : ∀ a : E, ‖a‖ = coefficientExtensionAbsoluteValue l E a)
    (V : Type v) [NormedAddCommGroup V] [NormedSpace E V]
    (J : Type t) [Countable J] (j₀ : J) (b : Module.Basis J E V)
    (c C : ℝ) (_hc : 0 < c) (_hcC : c ≤ C)
    (_hb : ∀ a : J →₀ E,
      c * (↑(a.support.sup (fun j ↦ ‖a j‖₊)) : ℝ) ≤ ‖b.repr.symm a‖ ∧
      ‖b.repr.symm a‖ ≤ C * (↑(a.support.sup (fun j ↦ ‖a j‖₊)) : ℝ)) :
    ∃ lam : V →L[E] E, lam.toLinearMap = b.coord j₀ ∧
      ∀ (H : Type w) [AddCommGroup H] [Module (V →L[E] V) H] [Module E H]
        [IsScalarTower E (V →L[E] V) H],
        (∃ S : Set H, S.Countable ∧ Submodule.span E S = ⊤) →
        ∃ Φ : (V ⊗[E] LinearMap.range
            (Module.toModuleEnd E H (lam.smulRight (b j₀)))) ≃ₗ[E] H,
          (∀ (v₀ : V) (h : LinearMap.range
              (Module.toModuleEnd E H (lam.smulRight (b j₀)))),
            Φ (v₀ ⊗ₜ[E] h) = (lam.smulRight v₀) • (h : H)) ∧
          (∀ (T : V →L[E] V) (v₀ : V) (h : LinearMap.range
              (Module.toModuleEnd E H (lam.smulRight (b j₀)))),
            Φ (T v₀ ⊗ₜ[E] h) = T • Φ (v₀ ⊗ₜ[E] h)) := by
  sorry

end Padic
