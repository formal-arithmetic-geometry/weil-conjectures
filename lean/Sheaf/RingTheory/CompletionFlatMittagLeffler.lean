/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q94
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Sheaf.RingTheory.IsMittagLeffler
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Sheaf.RingTheory.CompletedFreeFlatMittagLeffler
import Sheaf.SecTraceFormula.FlatProjectiveReductionCompletionSplitting

/-!
# Flat Mittag-Leffler completed modules

Source: Stacks Project, Algebra, Tag 05DK, lemma-lift-ML
(blueprint: lem-trf-completion-flat-mittag-leffler).
-/

@[expose] public section

universe u v w t

namespace Module

/-- Let `R` be a Noetherian commutative ring complete for an ideal `I`.  If `P` is
flat over `R` and `P / I P` is projective over `R / I`, then the `I`-adic
completion of `P` is flat and Mittag-Leffler over `R`.

Source: Stacks Project, Algebra, Tag 05DK, lemma-lift-ML.
Proof:
1. Form the free module `F = P →₀ R`. The evaluation map sending a finitely
   supported family to its linear combination of elements of `P` is surjective:
   the family supported at `p` with coefficient one maps to `p`. Its kernel gives
   a short exact sequence from that kernel through `F` to `P`.
2. Apply `lem-trf-flat-projective-reduction-completion-splitting` to this sequence,
   using flatness of `P` and projectivity of its reduction. The completed evaluation
   `r` has a section `s`, so `r ∘ s = id`. Tensoring these maps on either side
   preserves this identity, hence the induced maps from `s` remain split injective.
3. By `lem-trf-completed-free-flat-mittag-leffler`, the completion of `F` is flat
   and Mittag-Leffler, since `R` is Noetherian and complete. No finite generation
   of `P` or its underlying indexing set is required.
4. For an injective linear map `f : Q₁ → Q₂`, tensor a kernel element for
   `f ⊗ id` with `s`. Naturality identifies its image with zero in the tensor
   product with the completion of `F`. Flatness there makes that image zero;
   applying the tensor map from `r` gives the original element zero. Thus the
   completion of `P` is flat. The naturality identity holds on pure tensors and
   extends by the tensor universal property (`def-weil-pbc-module-tensor-product`).
5. For any family of modules, naturality of `TensorProduct.piRightHom` with
   respect to `s` sends its kernel into the corresponding kernel for the completion
   of `F`. That kernel is zero by its Mittag-Leffler property; applying the tensor
   map from `r` gives zero in the original domain. Naturality holds on pure tensors,
   with coordinate `s(p) ⊗ qⱼ`, and hence on all tensors by the same universal
   property. This includes the empty family. (blueprint: lem-trf-completion-flat-mittag-leffler) -/
theorem completion_flat_mittag_leffler
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (I : Ideal R) [IsAdicComplete I R]
    (P : Type v) [AddCommGroup P] [Module R P] [Module.Flat R P]
    [Module.Projective (R ⧸ I) (P ⧸ (I • (⊤ : Submodule R P)))] :
    Module.Flat R (AdicCompletion I P) ∧
      Module.IsMittagLeffler.{u, v, w, t} R (AdicCompletion I P) := by
  sorry

end Module
