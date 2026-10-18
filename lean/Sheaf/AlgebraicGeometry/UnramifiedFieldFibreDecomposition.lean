/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Finiteness.Defs

import WeilConjectures.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen
import Sheaf.AlgebraicGeometry.UnramifiedAlgebraOverFieldProduct
import Sheaf.AlgebraicGeometry.SpecFiniteProductFields
import WeilConjectures.Mathlib.RingTheory.Etale.Field
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Unramified schemes over a field as disjoint unions of finite separable spectra

Source: Stacks Project, Morphisms, Lemma 02G7 (lemma-unramified-over-field), part (1).
(blueprint: lem-trf-unramified-field-fibre-decomposition)
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A scheme over a field is unramified exactly when it is a disjoint union, over that field,
of spectra of finite separable field extensions. The index set may be empty or infinite.
Source: Stacks Project, Morphisms, Lemma 02G7 (lemma-unramified-over-field), part (1).
(blueprint: lem-trf-unramified-field-fibre-decomposition)

Proof:
1. Suppose the structure morphism is unramified. Choose an affine open cover of `X`.
   By `lem-weil-pbc-unramified-base-change-open`, restriction to each chart is unramified.
   By `lem-weil-pbc-unramified-algebra-over-field-product`, its algebra is a finite product
   of finite separable extensions of `k`, with the empty product allowed.
2. By `lem-weil-pbc-spec-finite-product-fields`, each factor spectrum is the singleton
   open subscheme belonging to its projection kernel. These singletons exhaust the chart.
   The identification is over `k`, since projection of the chart's algebra structure is
   precisely the factor's algebra structure, and `Spec.map` reverses composition.
3. Index the singleton open subschemes by the points of `X`. They are pairwise disjoint
   and cover `X`. For every open `V`, the sheaf axiom identifies its sections with the
   product of the sections on these singletons in `V`, compatibly with restrictions.
   Thus their coproduct is isomorphic to `X` as a scheme over `k`. For empty `X`, use
   the empty index set; no finiteness condition on the whole index set is needed.
4. Conversely, each finite separable extension has etale spectrum by
   `lem-weil-pbc-finite-separable-extension-etale`. By `def-weil-etale-morphism` this is
   unramified. The criterion `lem-weil-pbc-unramified-ring-map-iff-unramified-affine`
   gives finite type and vanishing relative differentials on every summand.
5. The summands form an affine open cover. The affine-cover formulation in
   `def-weil-unramified-morphism` now gives unramifiedness of the structure morphism.
   For the empty union the condition is vacuous. -/
theorem unramified_iff_exists_iso_coproduct_spec_finite_separable
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) :
    (LocallyOfFiniteType f ∧ IsOpenImmersion (pullback.diagonal f)) ↔
      ∃ (I : Type u) (L : I → Type u) (_ : ∀ i, Field (L i))
        (_ : ∀ i, Algebra k (L i)),
        (∀ i, Module.Finite k (L i) ∧ Algebra.IsSeparable k (L i)) ∧
          ∃ e : (∐ fun i : I ↦ Spec (.of (L i))) ≅ X,
            ∀ i : I, Sigma.ι (fun j : I ↦ Spec (.of (L j))) i ≫ e.hom ≫ f =
              Spec.map (CommRingCat.ofHom (algebraMap k (L i))) := by
  sorry

end AlgebraicGeometry
