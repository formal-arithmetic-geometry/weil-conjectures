/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q81
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Sheaf.AlgebraicGeometry.ExistsContinuousMapOfOpenSubcollection
import Sheaf.TraceFormula.DerivedBasisLocalExtSheaf

/-! # Negative Hom vanishing and unique gluing on an intersection-refining open cover

Source: Stacks Project, Cohomology, Tags 0D66(2) and 0D68, using Topology, Tag 0D5Q
(blueprint: lem-trf-derived-basis-local-hom-glue).

Restriction uses the localized open site, canonically equivalent to module sheaves on
`U.toScheme` by `Scheme.Modules.overEquiv U`. The shared `derivedOpenHomRestriction`
includes the comparison from iterated restriction to direct restriction. The bijection
is expressed by its singleton fibres: every inclusion-compatible family has exactly
one global preimage. No nonempty or finiteness condition is imposed on the cover.
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

/-- Negative cross Hom vanishing propagates to every union of members of an
intersection-refining open cover, and compatible local maps glue uniquely.
Source: Stacks Project, Cohomology, Tags 0D66(2), 0D68; Topology, Tag 0D5Q
(blueprint: lem-trf-derived-basis-local-hom-glue).

Proof:
1. Apply `lem-trf-derived-basis-open-subcollection-map` to obtain a continuous
   quotient map f with saturated members of C and their images a basis. A union O
   is also saturated and has open image, whose inverse image is O.
2. Give the target the direct-image ring sheaf f_* O_X. Pulling back a covering
   preserves unions and intersections, so its sheaf axiom follows from that of O_X
   (`def-weil-pbc-sites-and-cohomology`). The identity structural map makes f a
   ringed-space morphism; the target need not be a scheme or locally ringed.
3. Apply `lem-trf-derived-basis-local-ext-sheaf` (0D66(2)) to f and M,N.
   Saturation identifies its basiswise hypothesis with the given negative Hom
   vanishing. Its conclusions give vanishing on all inverse-image opens and a
   sheaf of degree-zero morphisms on the target.
4. Cover f(O) by the f(U) with U in C and U contained in O. Saturation identifies
   f(U) intersect f(V) with f(U intersect V), covered by the f(W) refining the
   intersection. Inclusion compatibility makes both restrictions agree on each
   f(W); sheaf separatedness makes them agree on the overlap. Sheaf gluing gives
   a unique section on f(O), hence the unique map on O. Restrictions of any map
   satisfy inclusion compatibility by composition of canonical restrictions.
5. The all-open clause of 0D66 gives negative Hom vanishing on O. On the empty
   open the empty-cover sheaf axiom gives a singleton Hom set. If X and C are
   empty, the quotient target and its basis are empty, so the same argument
   applies without a nonemptiness assumption. -/
theorem derived_basis_local_hom_glue
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (C : Set X.Opens) (hcover : sSup C = ⊤)
    (hrefine : ∀ U ∈ C, ∀ V ∈ C,
      sSup {W : X.Opens | W ∈ C ∧ W ≤ U ⊓ V} = U ⊓ V)
    (M N : schemeDerivedCategory X)
    (hnegative : ∀ U ∈ C, ∀ i : ℤ, i < 0 →
      Subsingleton
        ((SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj
            M ⟶
          ((SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj
            N)⟦i⟧)) :
    ∀ O : X.Opens, sSup {U : X.Opens | U ∈ C ∧ U ≤ O} = O →
      (∀ i : ℤ, i < 0 →
        Subsingleton
          ((SheafOfModules.overFunctor (moduleRings X.toRingedSpace) O).mapDerivedCategory.obj
              M ⟶
            ((SheafOfModules.overFunctor (moduleRings X.toRingedSpace) O).mapDerivedCategory.obj
              N)⟦i⟧)) ∧
      (∀ (a : ∀ U : {U : X.Opens // U ∈ C ∧ U ≤ O},
          (SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U.val).mapDerivedCategory.obj
              M ⟶
            (SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U.val).mapDerivedCategory.obj
              N),
        (∀ (U V : {U : X.Opens // U ∈ C ∧ U ≤ O}) (h : V.val ≤ U.val),
          derivedOpenHomRestriction X.toRingedSpace (homOfLE h) (a U) = a V) →
        ∃! f : (SheafOfModules.overFunctor (moduleRings X.toRingedSpace) O).mapDerivedCategory.obj
              M ⟶
            (SheafOfModules.overFunctor (moduleRings X.toRingedSpace) O).mapDerivedCategory.obj
              N,
          ∀ U : {U : X.Opens // U ∈ C ∧ U ≤ O},
            derivedOpenHomRestriction X.toRingedSpace (homOfLE U.property.2) f = a U) := by
  sorry

end AlgebraicGeometry
