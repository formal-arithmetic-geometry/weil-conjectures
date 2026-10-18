/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.RingTheory.Spectrum.Maximal.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Lifting a valuation ring through a flat morphism of schemes

Source: Stacks Project, Tag 089F, `lemma-lift-valuation-ring-through-flat-morphism`,
specialized to schemes; More on Algebra, `definition-extension-valuation-rings`.
(blueprint: lem-a1-flat-valuation-lifting)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A valuation-ring morphism whose closed point lies in the image of a flat morphism
lifts after an injective local extension of valuation rings.
Source: Stacks Project, Tag 089F, `lemma-lift-valuation-ring-through-flat-morphism`,
and More on Algebra, `definition-extension-valuation-rings`.
(blueprint: lem-a1-flat-valuation-lifting)

Proof:
1. A valuation ring is a local domain; write `s` for its closed point and `m` for its
   maximal ideal (`def-trf-valuation-ring`).
2. Form `Z = Y ×_T Spec R`. Choose `y` over `b(s)`. The tensor product of the residue
   fields of `y` and `s` over that of `b(s)` is nonzero
   (`lem-weil-common-extension-fields-tensor-nontrivial`), and has a maximal ideal
   (`lem-weil-common-extension-fields-maximal-ideal`). The fibre-product point correspondence
   (`lem-weil-pbc-fibre-product-points`) gives `z` over `y` and `s`
   (`def-pc-fibre-product`).
3. Flat base change (`lem-weil-pbc-flat-morphism-base-change`) and the stalkwise definition
   (`def-weil-flat-morphism`) give a flat local map `α : R → B = O_{Z,z}`, identifying
   the closed-point stalk of `Spec R` with `R`
   (`lem-weil-pbc-morphism-from-spec-local-ring`). Write `n` for the maximal ideal of `B`.
4. Since `m B ⊆ n`, the maximal-ideal criterion
   (`lem-weil-pbc-flat-faithfully-flat-maximal-ideals`) makes `α` faithfully flat.
   Surjectivity on spectra (`lem-weil-pbc-faithfully-flat-surjective-spectrum`) supplies
   a prime `q` of `B` over zero in `R`.
5. The quotient `B/q` is a local domain. A valuation ring `R'` of its fraction field
   dominating it exists by `lemma-nagata-local-domain-valuation-dominates`.
   The composite `β : B → B/q → R'` has inverse image of its maximal ideal equal to `n`.
6. Set `ι = β ∘ α`. Its kernel is zero because `q` lies over zero; it is local because
   the inverse image of the maximal ideal is `m`. The local-ring morphism correspondence
   (`lem-weil-pbc-morphism-from-spec-local-ring`) gives `d : Spec R' → Z` over `Spec R`.
   Composing with `Z → Y` gives `c`; the pullback identity gives the asserted square
   (`def-pc-fibre-product`, `def-weil-affine-spectrum`). -/
theorem exists_flat_valuation_lift {Y T : Scheme.{u}} (f : Y ⟶ T) [Flat f]
    (R : Type u) [CommRing R] [IsDomain R] [ValuationRing R]
    (b : Spec (CommRingCat.of R) ⟶ T)
    (h : b (IsLocalRing.closedPoint R) ∈ Set.range f) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : ValuationRing R')
      (ι : R →+* R'), Function.Injective ι ∧ IsLocalHom ι ∧
      ∃ c : Spec (CommRingCat.of R') ⟶ Y,
        c ≫ f = Spec.map (CommRingCat.ofHom ι) ≫ b := by
  sorry

end AlgebraicGeometry
