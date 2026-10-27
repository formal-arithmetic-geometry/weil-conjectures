/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q31
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Noetherian

import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.DirectSum.Module

/-!
# Local Noetherianity descends along an fppf morphism

Source: Stacks Project, Descent, Tag 034C (lemma-Noetherian-local-fppf),
the descent implication for a singleton fppf covering
(blueprint: lem-sfb-scheme-locnoeth-fppf-descent).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- Local Noetherianity descends along a flat, locally finitely presented, surjective
morphism of schemes. Source: Stacks Project, Descent, Tag 034C
(blueprint: lem-sfb-scheme-locnoeth-fppf-descent).

Proof plan:
1. Regard the singleton consisting of `f` as an fppf covering (def-pc-fppf-site).
   It is fpqc by lem-trf-fppf-covering-is-fpqc. For each affine open `V = Spec A`
   of `Y`, def-weil-pbc-fpqc-covering provides finitely many affine opens
   `U_j = Spec B_j` of `X` whose images have union exactly `V`.
2. Each `B_j` is Noetherian by pqf-lem-affine-open-locnoeth. The ring maps
   `A → B_j` supplied by def-weil-affine-spectrum are flat by
   lem-weil-pbc-flat-morphism-affine-criterion, applied to `(U_j, V)`.
3. The finite product `B` of the `B_j` is flat over `A` by
   lem-weil-pbc-finite-product-flat-modules. Every prime of `A` lifts to some
   `B_j` by the covering property, and then to `B` via the coordinate projection.
   Hence `A → B` is faithfully flat by
   lem-weil-pbc-flat-surjective-spectrum-faithfully-flat.
4. Every ideal of `B` is finitely generated: project to each Noetherian `B_j`,
   lift finite generators, and multiply the lifts by the coordinate idempotents.
   The resulting finite collection generates the ideal by coordinatewise summation.
   Thus `B` is Noetherian by def-weil-pbc-noetherian-ring; the empty product is
   the zero ring and satisfies the same assertion.
5. Apply lem-weil-pbc-faithfully-flat-descent-noetherian to conclude that `A`
   is Noetherian.
6. Every affine open of `Y` therefore has a Noetherian section ring, so
   pqf-def-locnoeth gives the conclusion. For empty `Y`, use the empty affine
   cover. Finiteness was needed only separately over each affine open of `Y`. -/
theorem isLocallyNoetherian_of_fppf
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Flat f] [LocallyOfFinitePresentation f] [Surjective f]
    [IsLocallyNoetherian X] : IsLocallyNoetherian Y := by
  sorry

end AlgebraicGeometry
