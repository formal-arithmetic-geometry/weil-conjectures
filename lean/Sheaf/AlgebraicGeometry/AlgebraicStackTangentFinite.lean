/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.AlgebraicGeometry.MarkedStackDeformations
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.DensePoints

/-! # Finite tangent spaces of algebraic stacks

Source: Stacks Project, artin.tex, Tag 07X1 (lemma-finite-dimension), tangent assertion
(blueprint: lem-sfb-algebraic-stack-tangent-finite).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.StackDeformation

variable {R k : Type u} [CommRing R] [IsNoetherianRing R] [Field k]
  [Algebra R k] [Algebra.FiniteType R k]
  (F : BasedCategory.{v, w} (Over (Spec (.of R))))
  (x : Functor.Fiber F.p (affine (CommAlgCat.of R k)))

/-- The canonical tangent space of a locally finite type algebraic stack is finite-dimensional.
Source: Stacks, artin.tex, Tag 07X1, lemma-finite-dimension, tangent-space assertion
(blueprint: lem-sfb-algebraic-stack-tangent-finite).

Proof:
1. By lem-sfb-algebraic-stack-rim-schlessinger and
lem-sfb-marked-deformation-tangent-field-extension, the marked category satisfies (RS).
This gives a unique isomorphism class of pair-lifts and the stated vector operations.
For a finite extension l/k it also gives T_x ⊗_k l ≅ T_(x_l).
2. Base change the smooth surjective atlas along x. An étale scheme chart of the
nonempty smooth algebraic space has a finite separable l-valued point by
lem-pc-dense-separable-points. Its lift u in U lies in an affine Spec B with B finite type
as an R-algebra. The finite extension l is still finite type over R.
3. For a marked dual-number deformation of x_l, base change the atlas and apply
lem-sfb-smooth-space-affine-infinitesimal-lift to its marked l-point. Both spectra have
one point, so the lifted map lands in Spec B. Its tangent map onto T_(x_l) is surjective.
4. A lift of B → l to B → l[ε] is exactly an R-derivation B → l. Evaluation on finitely
many R-algebra generators embeds these derivations linearly into l^n, also when n=0.
One must use algebra generators, not generators of the point ideal in the source's
last sentence; inseparable residue extensions otherwise invalidate that argument.
5. Pullback respects constant lifts and scaling. The map b ↦ φ₀(b)+ε₁d₁(b)+ε₂d₂(b)
shows compatibility with the pair-lift and sum operation. Hence the surjective tangent
map is linear and T_(x_l) is finite-dimensional.
6. A k-linear functional l → k taking 1 to 1 splits v ↦ v ⊗ 1. Since l/k is finite,
T_(x_l) is finite-dimensional over k, and its k-subspace T_x is finite-dimensional.
No properness, separatedness, smoothness over R, or stabilizer assumption is used. -/
theorem algebraicStack_tangent_finite
    (hF : IsAlgebraicModuliStack F)
    (U : Over (Spec (.of R)))
    (a : BasedFunctor (discreteModuli (yoneda.obj U)) F)
    (ha : IsSmoothModuliAtlas F U a) (hU : LocallyOfFiniteType U.hom) :
    ∃ (_ : AddCommGroup (Tangent F x)) (_ : Module k (Tangent F x)),
      FiniteDimensional k (Tangent F x) ∧
      (∀ t : Tangent F x, IsZeroClass F x t ↔ t = 0) ∧
      (∀ (c : k) (t s : Tangent F x), IsScalarClass F x c t s ↔ s = c • t) ∧
      (∀ t s r : Tangent F x, IsSumClass F x t s r ↔ r = t + s) ∧
      ∀ t s : Tangent F x,
        ∃ Z : Marked F x (ArtinDeformation.squareZeroTest (R := R) (k := k) (k × k)),
          IsPairLift F x t s Z ∧
            ∀ Z' : Marked F x
              (ArtinDeformation.squareZeroTest (R := R) (k := k) (k × k)),
              IsPairLift F x t s Z' → Nonempty (Z ≅ Z') := by
  sorry

end AlgebraicGeometry.StackDeformation
