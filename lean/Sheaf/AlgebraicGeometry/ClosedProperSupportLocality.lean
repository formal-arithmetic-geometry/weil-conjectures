/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import Sheaf.AlgebraicGeometry.FpqcFinerThanEtale
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Sites.Etale
import Sheaf.AlgebraicGeometry.ProperMorphismFpqcDescent

/-!
# Base change and étale descent of closed proper supports

Source: Stacks Project, Tags 0CYP and 0F4J
(blueprint: lem-cbc-closed-proper-support-locality).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Closed subsets proper over the base remain proper after any base change, and
properness descends along any jointly surjective étale family. No quasi-compactness
of the ambient morphism, base, or covering members is assumed.
Source: Stacks Project, Tags 0CYP and 0F4J.
(blueprint: lem-cbc-closed-proper-support-locality)

Proof:
1. Give `C` its reduced induced closed structure `Z` using
   `lem-weil-pbc-reduced-induced-closed-subscheme`. The base change of `Z` is a closed
   subscheme of the base change of `T` (`lem-weil-pbc-closed-immersion-base-change`).
   Its image is the inverse image of `C`: restrict to affine opens using
   `lem-weil-pbc-open-fibre-product` and `lem-weil-pbc-fibre-product-affine-spectra`.
   There the tensor quotient `(R/I) ⊗[R] B` is `B/IB`, whose primes contract into `V(I)`.
2. The ambient projection remains locally of finite type (`lem-weil-pbc-lft-base-change`).
   Properness of `Z` is preserved by `lem-weil-pbc-proper-base-change`. Independence
   of the closed structure (`lem-weil-pbc-closed-subset-proper-over-base-properties`)
   gives properness of the inverse-image subset, without asserting its structure is reduced.
3. A jointly surjective étale family covers the identity in the small étale site
   (`def-weil-pbc-etale-site`), hence is fpqc by `lem-weil-pbc-fpqc-finer-than-etale`.
   Its pullbacks of `Z` have the prescribed supports by step 1. Their properness follows
   from the hypothesis and independence of closed structure as in step 2.
4. Apply `lem-weil-pbc-proper-morphism-fpqc-descent` to `Z` over `S`. This makes
   `Z → S` proper, which is exactly `IsClosedSubsetProperOver p C`.
-/
theorem closed_proper_support_locality
    {T S : Scheme.{u}} (p : T ⟶ S) [LocallyOfFiniteType p]
    (C : TopologicalSpace.Closeds T) :
    (∀ (S' : Scheme.{u}) (w : S' ⟶ S), IsClosedSubsetProperOver p C →
      IsClosedSubsetProperOver (pullback.snd p w)
        (C.preimage (pullback.fst p w).continuous)) ∧
    (∀ (I : Type v) (Sᵢ : I → Scheme.{u}) (w : ∀ i, Sᵢ i ⟶ S)
      [∀ i, Etale (w i)],
      (∀ s : S, ∃ (i : I) (x : Sᵢ i), w i x = s) →
      (∀ i, IsClosedSubsetProperOver (pullback.snd p (w i))
        (C.preimage (pullback.fst p (w i)).continuous)) →
      IsClosedSubsetProperOver p C) := by
  sorry

end AlgebraicGeometry.Scheme
