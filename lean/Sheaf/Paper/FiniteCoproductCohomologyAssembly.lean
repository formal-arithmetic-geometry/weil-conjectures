/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Mathlib.AlgebraicGeometry.Limits
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.CohomologyMap

/-! # Cohomology of a finite coproduct is the product of component cohomologies

Source: literature/stacks-project/etale-cohomology.tex, first paragraph of the proof of
Lemma 0A5B (blueprint: lem-weil-pbc-finite-coproduct-cohomology-assembly)

The restriction maps along the coprojections of a finite disjoint coproduct identify
étale cohomology with the product of the component cohomology groups.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- For a finite coproduct of schemes, étale cohomology is the product of the
component cohomologies, via restriction along the coprojections.

Source: literature/stacks-project/etale-cohomology.tex, first paragraph of the proof of
Lemma 0A5B (blueprint: lem-weil-pbc-finite-coproduct-cohomology-assembly).
Proof:
1. By `lem-weil-pbc-scheme-coproduct-family`, the coprojections are disjoint clopen
   immersions covering the coproduct; every étale object restricts componentwise.
2. The sheaf condition gives the equivalence with the product of the component
   sheaf categories (`lem-weil-pbc-etale-sheaf-clopen-product`), using
   `def-weil-pbc-inverse-image` for restriction. Global sections become the product
   of component global sections.
3. The sheaf categories have enough injectives
   (`lem-weil-pbc-module-sheaves-enough-injectives`). Global sections are additive
   and left exact (`def-weil-pbc-global-sections-functor`). An injective resolution
   is bounded below and K-injective (`lem-weil-pbc-bounded-below-injectives-kinjective`),
   so `def-weil-pbc-etale-cohomology` is the right derived functor of global sections
   (`def-sp-left-exact-additive`). The equivalence carries injective resolutions
   componentwise; `lem-weil-pbc-derived-finite-product` computes their derived
   global sections as the product. The resulting isomorphism is induced by the
   restriction maps displayed here.
-/
theorem finiteCoproductCohomologyAssembly
    {I : Type u} [Finite I] (X : I → Scheme.{u}) (C : Scheme.{u})
    (ι : ∀ i : I, X i ⟶ C) (hc : IsColimit (Cofan.mk C ι))
    (F : Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    Function.Bijective
      (fun x : Sheaf.H F q =>
        fun i : I =>
          cohomologyMap (ι i) F q x) := by
  sorry

end AlgebraicGeometry.Etale
