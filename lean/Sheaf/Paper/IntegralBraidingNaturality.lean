/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.Paper.DerivedPullbackTensorConstraints
import Sheaf.Paper.CoefficientRingedSequenceSite
import Sheaf.Paper.CompletedPullbackTensorComparison
import Sheaf.Paper.ShiftedTensorMorphismCalculus
import Sheaf.Paper.DerivedPullbackTensorHom
import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
import Sheaf.Paper.IntegralSystemReductionFullyFaithful

/-! # Naturality of the integral Koszul braiding

Source: literature/stacks-project/sites-cohomology.tex, Tag 0FPQ
(lemma-symmetric-monoidal-cat-complexes), signed total symmetry and its naturality;
specialization to the coherently reduction-normalized completed integral tensor
(blueprint: lem-pur-integral-braiding-naturality).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory Opposite AlgebraicGeometry

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (W : Scheme.{u})
  [∀ w : W, Invertible (l : W.residueField w)]

/-- The coherently normalized integral Koszul braiding is natural in both inputs.

Source: literature/stacks-project/sites-cohomology.tex, Tag 0FPQ
(lemma-symmetric-monoidal-cat-complexes), signed total symmetry and its naturality;
(blueprint: lem-pur-integral-braiding-naturality).

Proof: coherent reduction of the completed integral tensor is functorial in both
arguments by [def-weil-derived-pullback-tensor-hom], and its reduction/tensor
comparison is natural by [def-pur-completed-pullback-tensor-comparison] and
[lem-coef-derived-system-evaluation-calculus]. The strict-system braiding is
natural by [def-pur-ringed-site-signed-tensor-models], with the Koszul sign on
homogeneous bidegrees. Conjugating by the comparisons gives equality after
reduction. Full faithfulness of coherent reduction, supplied by
[lem-pod-integral-system-reduction-fully-faithful], lifts this equality to the
integral category. The argument includes identity and zero arrows and the zero
object, with no extra finite-field, perfectness, boundedness or torsion-free
hypothesis beyond the constructible integral category.
-/
theorem pullbackTensorIntegralBraiding_naturality
    (M M' N N' : sfIntegralConstructibleCategory l E W)
    (a : M ⟶ M') (b : N ⟶ N') :
    (constructibleIntegralTensor l E W).map (Prod.mkHom a b) ≫
        (pullbackTensorIntegralBraiding l E W M' N').hom =
      (pullbackTensorIntegralBraiding l E W M N).hom ≫
        (constructibleIntegralTensor l E W).map (Prod.mkHom b a) := by
  sorry

end WeilConjectures
