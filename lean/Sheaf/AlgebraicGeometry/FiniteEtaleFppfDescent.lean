/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NF
-/
module

public import Sheaf.AlgebraicGeometry.FiniteEtaleCoverDescent
import Sheaf.AlgebraicGeometry.FppfFamilyCoproductDescentEncoding
import WeilConjectures.AlgebraicGeometry.AffineFpqcDescent
import WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover
import WeilConjectures.AlgebraicGeometry.FpqcDescentEtale

/-! # Effective fppf descent of finite étale schemes

Source: Stacks Project, Examples of Stacks, Tag 0BLZ
(blueprint: lem-sfb-finite-etale-fppf-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Finite étale schemes, with all base morphisms, satisfy effective descent for arbitrary
fppf covering families. The projections and compatibility equations identify the asserted
functor as pullback, including its overlap isomorphisms and its action on every morphism.
Its essential surjectivity gives compatible local trivializations of every datum, and its
full faithfulness gives unique descent of all compatible morphism families.
Source: Stacks Project, Examples of Stacks, Tag 0BLZ
(blueprint: lem-sfb-finite-etale-fppf-descent).

Proof plan, following the node and the source:
1. Base change preserves finiteness and étaleness
   (`def-weil-pbc-finite-etale-category`). Identify the two overlap pullbacks with the
   common fibre product (`def-pc-fibre-product`). The universal property proves the
   cocycle, and proves that pullback of any morphism respects it. The first projections
   satisfy `FiniteEtaleCoverDescentCompatible`.
2. The family is fpqc (`lem-trf-fppf-covering-is-fpqc`). Pulling it back to any source
   scheme remains fpqc (`lem-galois-fpqc-covering-base-change`). Subcanonicity gives
   unique descent of compatible maps (`lem-weil-pbc-fpqc-representable-descent`).
   Their composites to the base agree locally and hence globally. The fibre-product
   universal property identifies their pullbacks with the original local maps. This
   proves full faithfulness without requiring the morphisms to be invertible.
3. For a given datum, use `lem-trf-fppf-family-coproduct-descent-encoding` to form the
   singleton datum on the coproducts. Its local structure map is affine since finite
   maps are affine (`def-weil-finite-integral-morphism`), the coproduct inclusions form
   an open cover (`lem-weil-pbc-scheme-coproduct-family`), and affineness is local on
   the target (`pqf-lem-affine-local-target`). No finiteness of the index is used and
   no quasi-compactness of the coproduct map is asserted. If an index exceeds the
   scheme universe, first refine by a small affine subcover of the base and its sources;
   the fully faithful morphism descent of step 2 recovers all original components.
4. Apply `lem-galois-fpqc-affine-descent-effective` to this affine singleton datum.
   The final clause of `lem-trf-fppf-family-coproduct-descent-encoding` identifies its
   effectivity with compatible Cartesian squares for the original family.
5. The local pullbacks of the resulting global scheme are finite étale. Descend
   finiteness (`lem-weil-pbc-fpqc-descend-finite`) and étaleness
   (`lem-galois-fpqc-descend-etale`) along the original fpqc family. This proves
   essential surjectivity in the finite étale category.
6. Choose preimages and compatible isomorphisms for each datum. Full faithfulness
   uniquely defines the inverse on morphisms and proves the functor laws and
   naturality, yielding equivalence (`def-weil-size-convention`). The empty covering
   forces an empty base; empty local schemes and nonconstant ranks cause no change.
   No quasi-compactness or noetherian hypothesis on the base was used. -/
theorem finiteEtale_fppf_descent
    {I : Type (u + 1)} (T : Scheme.{u}) (U : I → Scheme.{u})
    (f : ∀ i, U i ⟶ T)
    (hcov : Presieve.ofArrows U f ∈ Scheme.fppfPrecoverage T) :
    ∃ (F : (MorphismProperty.Over (@IsFinite ⊓ @Etale) ⊤ T) ⥤ FiniteEtaleCoverDescent f)
      (q : ∀ P i, ((F.obj P).obj.localScheme i).left ⟶ P.left),
      FiniteEtaleCoverDescentCompatible F q ∧ Nonempty F.IsEquivalence := by
  sorry

end AlgebraicGeometry
