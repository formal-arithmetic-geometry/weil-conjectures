/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.GroupTheory.MonoidLocalization.Away
public import Sheaf.RingTheory.PresentationFittingIdeal

/-!
# Fitting ideal factorization after an etale localization

Source: literature/stacks-project/flat.tex, Tag 0812
(blueprint: lem-trf-etale-fitting-trick).
-/

@[expose] public section

universe u v

namespace AlgebraicGeometry

/--
The zeroth kernel-minor ideal of a quotient of a finite free algebra factors after an
étale localization. Source: Stacks Project, Tag 0812 (blueprint: lem-trf-etale-fitting-trick).

Proof plan: Set `B = C_h` and split `C ⊗[A] B` using the etale multiplication-map
splitting. The quotient by `K` becomes a direct sum `(B / K B) ⊕ (D / H)`. Apply
presentation Fitting-ideal base change and the direct-sum formula to obtain
`I₀(π) B = (K B) L`. Finite generators for `K` and a basis of `C` give finite
presentations of both summands; expansion of determinants in a finite relation list
then shows that `I₀(π)` and `L` are finitely generated.
-/
theorem exists_fg_fitting_factor
    (A : Type u) (C : Type v) [CommRing A] [CommRing C] [Algebra A C]
    (d : ℕ) (b : Module.Basis (Fin d) A C) (h : C)
    [AlgebraicGeometry.Etale
      (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom
          (RingHom.ulift.{max u v, max u v, u, v}
            (algebraMap A (Localization.Away h)))))]
    (K : Ideal C) (n : ℕ)
    (π : (Fin n → A) →ₗ[A] C ⧸ K) (hπ : Function.Surjective π) :
    ∃ (L : Ideal (Localization.Away h)),
      Ideal.map (algebraMap A (Localization.Away h))
          (π.presentationFittingIdeal 0) =
        Ideal.map (algebraMap C (Localization.Away h)) K * L ∧
      (K.FG → (π.presentationFittingIdeal 0).FG ∧ L.FG) := by
  sorry


end AlgebraicGeometry
