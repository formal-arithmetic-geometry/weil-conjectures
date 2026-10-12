/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex

/-! # Pullback cohomology on a locus with one locally free cohomology sheaf

Source: the cohomology-sheaf gluing argument in the proof of the perfect-locus lemma,
and Stacks Project, Tag 0B9S (blueprint: lem-pc-derived-pullback-single-cohomology).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- On a locus where a connective derived object has locally free cohomology in one
nonnegative degree only, derived pullback cohomology is ordinary pullback cohomology.

Source: blueprint lem-pc-perfect-locus, proof, cohomology-sheaf gluing paragraph and
termwise pullback paragraph; Stacks Project, Tag 0B9S and its perfect-locus input.
(blueprint: lem-pc-derived-pullback-single-cohomology).

Proof: let W be the union of the neighbourhoods in the hypothesis. On each such
neighbourhood all integer cohomology except degree i vanishes: negative degrees vanish
by connectivity and restriction is exact, and nonnegative degrees by the given condition.
The standard truncation maps therefore identify E on that neighbourhood with H^i(E)
placed in degree i. These identifications are canonical through truncation and agree on
overlaps, giving the same identification on W. The local finite freeness makes H^i(E)|W
flat, so its shifted single complex computes its derived pullback by ordinary pullback.
The morphism g factors through W since its entire image is in W. Apply derived pullback
composition to this factorization, then take degree-i cohomology. Exactness of open
restriction and the ordinary pullback composition identification give the claimed global
isomorphism. No common rank for the neighbourhoods is required. Empty image and rank
zero are included: all constructions restrict and glue also on the empty open. -/
theorem nonempty_homology_derivedPullback_iso_of_locally_single
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {T T' : Scheme.{u}} (g : T' ⟶ T) (E : schemeDerivedCategory T) (i : ℕ)
    (hneg : ∀ n : ℤ, n < 0 → IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings T.toRingedSpace)) n).obj E))
    (hloc : ∀ t ∈ Set.range g.base, ∃ U : T.Opens, t ∈ U ∧ ∃ r : ℕ,
      IsFiniteLocallyFreeInDegree
        (fun q : ℕ ↦ (Modules.restrictFunctor U.ι).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings T.toRingedSpace)) q).obj E)) i r) :
    Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) i).obj
        ((derivedPullback g).obj E) ≅ (Modules.pullback g).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings T.toRingedSpace)) i).obj E)) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
