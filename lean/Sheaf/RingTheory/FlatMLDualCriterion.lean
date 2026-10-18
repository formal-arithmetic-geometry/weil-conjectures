/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q102
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Sheaf.RingTheory.IsMittagLeffler
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures
import Mathlib.LinearAlgebra.TensorProduct.Map
import Sheaf.TraceFormula.MittagLefflerEventualDomination

/-!
# The dual finite-free system criterion for flat Mittag-Leffler modules

Source: Stacks Project, Algebra, Tag 059G (remark-flat-ML), with the directed-index
Mittag-Leffler condition of Tag 0595 (definition-ML-system)
(blueprint: lem-trf-flat-ml-dual-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u v w s t

open CategoryTheory CategoryTheory.Limits

namespace Module

/-- A flat module presented as a directed colimit of finite free modules is
Mittag-Leffler if the images of the dual transition maps eventually stabilize.
The module `M` is the cocone vertex `c.pt`; its compatible maps are `c.ι.app i`,
and `hc` says that these maps exhibit it as the colimit. The map
`(F.map (homOfLE hij)).hom.dualMap` sends a functional to its precomposition
with the transition map from `i` to `j`. The conclusion uses the tensor-product
Mittag-Leffler predicate, with arbitrary product-index and test-module universes `s` and `t`.

Source: Stacks Project, Algebra, Tags 059G and 0595
(blueprint: lem-trf-flat-ml-dual-criterion).

Proof:
1. Fix `i` and choose `j ≥ i` by the dual image-stabilization hypothesis. Choose a
   finite basis `(e_a)` of `F.obj j`, with coordinate maps `ε_a`. For each `k ≥ j`,
   lift each `ε_a ∘ f_ij` through the dual map of `f_ik`, obtaining `λ_a,k`.
   Define `h_k(y) = ∑ a, λ_a,k(y) • e_a`. Basis expansion gives
   `h_k ∘ f_ik = f_ij`. For rank zero this is the zero map into the zero module.
2. For any module `L` and `z ∈ ker (f_i ⊗ id_L)`, tensor-colimit compatibility
   (lem-weil-pbc-tensor-commutes-with-colimits) and the zero-at-a-stage criterion
   (lem-weil-pbc-filtered-colimit-modules-elementwise) give a stage `k₀ ≥ i`
   killing `z`. Choose a common upper bound `k ≥ k₀, j`; tensor functoriality
   (def-weil-pbc-module-tensor-product) shows that `f_ik ⊗ id_L` also kills `z`.
3. Tensor the factorization of step 1: `f_ij ⊗ id_L` kills `z`. Thus
   `ker (f_i ⊗ id_L) ≤ ker (f_ij ⊗ id_L)` for every `L`, with `j` independent
   of `L` and `z`; this is the required eventual domination.
4. Finite free modules are finitely presented (def-sc-finitely-presented-module).
   Apply lem-trf-mittag-leffler-eventual-domination to obtain the tensor-product
   Mittag-Leffler condition (def-trf-mittag-leffler-module). For larger test or
   product-index universes, lift the same presentation to a common universe;
   the colimit and the factorization identities are preserved. The flatness
   assumption is retained as in Tag 059G, although the presentation already implies it. -/
theorem isMittagLeffler_of_dual_images_stabilize
    (R : Type u) [CommRing R]
    {I : Type v} [PartialOrder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (F : I ⥤ ModuleCat.{max u v w} R)
    [∀ i : I, Module.Free R (F.obj i)] [∀ i : I, Module.Finite R (F.obj i)]
    (c : Cocone F) (hc : IsColimit c) [Module.Flat R c.pt]
    (hdual : ∀ i : I, ∃ (j : I) (hij : i ≤ j), ∀ (k : I) (hjk : j ≤ k),
      LinearMap.range (F.map (homOfLE (hij.trans hjk))).hom.dualMap =
        LinearMap.range (F.map (homOfLE hij)).hom.dualMap) :
    Module.IsMittagLeffler.{u, max u v w, s, t} R c.pt := by
  sorry

end Module
