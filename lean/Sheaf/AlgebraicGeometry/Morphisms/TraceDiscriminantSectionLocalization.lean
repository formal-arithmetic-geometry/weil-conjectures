/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J3
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.TraceDiscriminantSectionIdeal
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Localization of the explicit discriminant section ideal

Source: Stacks Project, Tag 0BVH, construction before Lemma 49.3.1.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The explicitly defined family of discriminant section ideals localizes.

Source: Stacks Project, Tag 0BVH, construction before Lemma 49.3.1.
(blueprint: lem-sbc-trace-discriminant-section-localization)

Proof: Cover an affine chart U by principal affine opens where the finite flat
section algebra is free. Such a cover exists because A is Noetherian, B is finite
flat and therefore finitely presented, and finite flat modules over local rings are
free. On each free chart the intersection defining traceDiscriminantSectionIdeal
is precisely the principal discriminant ideal: the chart itself gives one inclusion,
and trace base change and basis-change invariance give the other. These local ideals
agree on common affine refinements, by the same trace and basis-change calculation.
Thus the intersection is the module of sections satisfying this local ideal condition.
For a basic open D(r) the condition restricts, proving the forward inclusion. For the
reverse inclusion, write a section on D(r) as a fraction s/r^a. Take a finite principal
free cover of U. On each chart, localization membership in its discriminant ideal
means some power of r times s belongs to that ideal. Choose the maximum of the
finitely many exponents. The resulting section lies in every chart ideal and hence,
by compatibility and the sheaf condition, in every free subchart ideal. It therefore
lies in the defining intersection on U and maps to the original section after
multiplication by the inverse of a power of r. This proves equality of ideals.
Only compactness of affine U is used, not quasi-compactness of Y. If D(r) is empty,
its section ring is the zero ring, so the assertion is automatic. -/
theorem traceDiscriminantSectionIdeal_map_basicOpen
    {X Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [IsFinite f] [Flat f] (U : Y.affineOpens) (r : Γ(Y, U.1)) :
    (traceDiscriminantSectionIdeal f U).map
      (Y.presheaf.map (homOfLE (Y.basicOpen_le r)).op).hom =
        traceDiscriminantSectionIdeal f (Y.affineBasicOpen r) := by sorry

end AlgebraicGeometry.Scheme
