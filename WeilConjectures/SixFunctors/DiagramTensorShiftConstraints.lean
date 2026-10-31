/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.DiagramPullbackShiftData

/-! # DiagramTensorShiftConstraints

Resolving-model step for the simultaneous diagram-site comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genCtorIdx false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] SheafOfModules.monoidalCategory
  SheafOfModules.siteDerivedTensorIndependentCoefficients
  SheafOfModules.KFlatFixedTensor.representativeIso
  CategoryTheory.Functor.mapDerivedCategory
  HomologicalComplex₂.total

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory.CochainPullback
open SheafOfModules.DerivedTensorConstraints

namespace WeilConjectures.DiagramPullbackShift

variable (A : ℕ → CommRingCat.{u + 1}) (δ : ∀ n : ℕ, A (n + 1) ⟶ A n)

/-- On each simultaneous ringed sequence site the normalized tensor constraints
admit the action unitors and satisfy all intrinsic integer-shift identities.
Source: Stacks sites-cohomology.tex, lemma-symmetric-monoidal-cat-complexes (0FPQ)
and lemma-symmetric-monoidal-derived (0FPT); more-algebra.tex, item-shift-tensor.
(blueprint: lem-pur-diagram-tensor-shift-constraints).

Proof: take the uniquely normalized shift, associator and symmetry constraints
from existsUnique_derived_tensor_constraints. The ring in degree zero is resolving:
tensoring with the ring is isomorphic to the identity, and the bounded flat complex
is K-flat. Localize the unsigned chain action unitors and extend them naturally
using faithful restriction on resolving inputs. Their representative equations
are the definitions of these extensions. On resolving pairs the shift maps are
chainShift, so the single-slot zero and addition equations are the bifunctor shift
laws. Extracting the second shift followed by the first gives extraction;
interchanging them gives the scalar (-1)^(ab). On three resolving inputs the two
associator exponents are bp+c(p+q) and cq+(b+c)p, equal by distributivity.
The symmetry exponents bp+(p+a)(q+b) and ab+pq+aq differ by 2bp. For either
action unitor the ring input has degree zero, hence coefficient one. These chain
equalities descend through the specified representative comparisons, first on
resolving inputs and then on all inputs by faithful finite-variable restriction.
This argument includes negative shifts and arbitrary nonflat coefficient transitions. -/
theorem diagramTensorShiftConstraints (W : Scheme.{u}) :
    ∃ T : TensorConstraints A δ W, TensorCoherence A δ T := by sorry

end WeilConjectures.DiagramPullbackShift
