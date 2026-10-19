/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Adjunction.Limits
import Sheaf.RingTheory.Flat.LazardPresentation
import Sheaf.RingTheory.FiniteFreeMapResidueLocalizationStrong
import Sheaf.RingTheory.ProjectiveOverLocalFree

/-! # Local residue-field criterion for universal injectivity

Source: Stacks Project, Algebra, Tag 05FQ, lemma universally-injective-local
(blueprint: lem-trf-local-universal-injective-residue).
-/

@[expose] public section

universe u v w z

open scoped TensorProduct

namespace Module

/--
Let `(R, 𝔪)` be a commutative local ring and let `u : M →ₗ[R] N` be an `R`-linear
map.  If `M` is projective, `N` is flat, and the map induced by `u` on the
residue-field tensor products is injective, then tensoring `u` with any
`R`-module is injective.  The residue-field tensor products are the canonical
realizations of `M / 𝔪 M` and `N / 𝔪 N`.

Source: Stacks Project, Algebra, Tag 05FQ, lemma universally-injective-local
(blueprint: lem-trf-local-universal-injective-residue).

Proof:
1. By lem-trf-projective-over-local-free (Stacks Tag 0593), choose a basis of `M`,
   without any finiteness assumption on its index set.
2. Every finite basis span `P` is a direct summand, so its residue map into `N`
   is injective. Every tensor in `L ⊗[R] M` comes from one such finite span,
   by taking the union of the finite supports in a finite sum of pure tensors.
   It therefore suffices to prove universal injectivity on each finite span.
3. Flatness and lem-weil-pbc-tensor-right-exact show that tensoring with `N`
   preserves short exact sequences. Apply lem-kun-lazard-flat-module to write
   `N` as a nonempty directed colimit of finite free modules `F i`.
4. By lem-weil-pbc-filtered-colimit-modules-elementwise, lift the images of
   the finite basis of `P` to a common stage `F i`. For rank zero choose any
   stage. At every later stage `j`, the induced map `v j : P → F j` has
   injective residue map, since its composite with the colimit map is the
   original residue map.
5. Identify the residue-field tensor product with the quotient modulo the
   maximal ideal: the forward map sends `ā ⊗ x` to `a • x` modulo the ideal,
   and the inverse sends the class of `x` to `1 ⊗ x`. The scalar relations
   make both maps well-defined, and they are inverse and natural in `x`.
6. Apply lem-pc-finite-free-map-residue-localization-strong to each `v j`.
   It splits after inverting some element outside the maximal ideal. That
   element is a unit in the local ring, so localization changes neither
   module and `v j` itself splits. Tensoring its left inverse proves
   injectivity of `L ⊗ v j`, for every `L` and every `j ≥ i`.
7. By lem-weil-pbc-tensor-commutes-with-colimits, tensoring the Lazard cocone
   with `L` is still colimiting. If a tensor in `L ⊗ P` maps to zero in
   `L ⊗ N`, its image at stage `i` is zero at a later stage, by the zero
   detection clause of lem-weil-pbc-filtered-colimit-modules-elementwise.
   Step 6 then makes it zero already in `L ⊗ P`. Step 2 finishes for `M`.
-/
theorem universallyInjective_of_residueField_injective
    {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Projective R M]
    {N : Type w} [AddCommGroup N] [Module R N] [Module.Flat R N]
    (u : M →ₗ[R] N)
    (hres : Function.Injective (u.lTensor (IsLocalRing.ResidueField R))) :
    ∀ (L : Type (max u v w z)) [AddCommGroup L] [Module R L],
      Function.Injective (u.lTensor L) := by
  sorry

end Module
