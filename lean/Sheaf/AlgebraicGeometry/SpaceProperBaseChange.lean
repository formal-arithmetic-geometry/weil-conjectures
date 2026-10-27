/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.TraceFormula.SpaceQCSeparatedEtaleLocal
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite

/-!
# Base change of proper algebraic-space morphisms

Source: Stacks Project, Morphisms of Spaces, Tag 04WP (lemma-base-change-proper),
with the properness definition Tag 03ZM
(blueprint: lem-sfb-space-proper-base-change).

The morphism in the conclusion is the second projection of the actual sheaf fibre
product, bundled in the full subcategory of algebraic spaces. Properness uses the
existing separated, finite-type and universally closed predicates.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Properness is preserved by arbitrary algebraic-space base change, without
Noetherian, finite-presentation or representability assumptions on either morphism.
Source: Stacks Project, Morphisms of Spaces, Tag 04WP, with Tags 03KL, 03XH and 03IS
(blueprint: lem-sfb-space-proper-base-change).

Proof: (1) Put X' = X ×_Y Y', H = X ×_Y X and H' = X' ×_{Y'} X'. The projections
induce H' → H. For a scheme T → H' with coordinates (x1,x2,y'), the scheme test
X ×_H T of the old diagonal identifies with X' ×_{H'} T by (x,t) ↦ ((x,y'(t)),t);
its inverse forgets y'. These maps are natural on test schemes and preserve the
projections to T. Thus each scheme test of the new diagonal is the old diagonal's
closed immersion. This proves separatedness, using
lem-trf-space-fibre-products-etale-covers.
(2) Properness supplies finite type. Apply arbitrary-base-change preservation and
algebraic-space compatibility in lem-sfb-stack-finite-type-calculus to the discrete
stacks associated to X,Y,Y'. It gives local finite type and quasi-compactness of
the new projection. The quasi-compact scheme-atlas convention is that of
lem-trf-space-qc-separated-etale-local; for algebraic spaces it agrees with compactness
of the atlas-topology point space (Stacks, Properties of Spaces, Tag 03E4).
(3) For any algebraic space T → Y', the sheaf universal property identifies
(X ×_Y Y') ×_{Y'} T with X ×_Y T over T: both classify matching pairs (x,t).
The projection on the right is closed on points by universal closedness of f.
The displayed isomorphism induces a homeomorphism on point spaces: composition
with it and its inverse bijects the representable etale scheme charts, so the
final-topology open-set criterion of def-a1-space-point-topology agrees on both
sides. Hence every base change of the new projection is closed on points.
(4) The separatedness, finite type and universal closedness from (1)--(3) are
exactly the three conjuncts of MapIsProper. -/
theorem proper_baseChange {B : Scheme.{u}} {X Y Y' : AlgebraicSpace B}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (hf : MapIsProper f) :
    MapIsProper
      (ObjectProperty.homMk (Limits.pullback.snd f.hom g.hom) :
        enlargedFibreProduct f g ⟶ Y') := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
