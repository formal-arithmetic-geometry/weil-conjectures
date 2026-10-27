/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NE
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointClasses
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # Separated algebraic-space morphisms and universally closed diagonals

Source: Stacks Project, Morphisms of Spaces, Tag 04Y0, equivalence (1) and (2)
(blueprint: lem-sfb-space-separated-diagonal-closed).

The target of the diagonal is the sheaf fibre product, bundled as an algebraic space
using the existing fibre-product theorem. No finiteness hypothesis is imposed.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is separated exactly when its diagonal is universally
closed. Separatedness means that every scheme test of the diagonal is a closed immersion;
universal closedness tests closed maps of point spaces after all algebraic-space base changes.
Source: Stacks Project, Morphisms of Spaces, Tag 04Y0, equivalence (1) and (2)
(blueprint: lem-sfb-space-separated-diagonal-closed).

Proof:
1. A separated map has a closed-immersion diagonal. By
   lem-sfb-space-closed-subspace-proper this diagonal is proper, hence universally closed.
2. Conversely, assume the diagonal is universally closed. By
   lem-sfb-space-diagonal-scheme-tests every scheme test of it is represented by a
   locally finite type monomorphism d : D → T. The point space of a scheme is its
   underlying topological space: sending a point to its residue-field representative
   is bijective, since field points factor through residue fields and equivalent
   field points have the same image. The final topology agrees with the Zariski
   topology: the identity chart tests openness, and every etale chart is continuous
   (def-a1-space-point-topology and def-a1-algebraic-space-point-classes).
   For every T' → T, fibre-product pasting identifies D ×_T T' with the test of the
   original diagonal along T' (lem-trf-space-fibre-products-etale-covers).
   Universal closedness therefore implies scheme universal closedness of d
   (def-weil-proper-morphism).
3. The scheme map d is separated by lem-trf-scheme-monomorphism-separated and
   quasi-compact by lem-weil-pbc-universally-closed-quasi-compact. Together with its
   local finite type property this is finite type (def-weil-finite-type-morphism),
   hence proper (def-weil-proper-morphism). By lem-pc-proper-monomorphism-closed,
   d is a closed immersion. All scheme tests have this property, so the diagonal
   is a closed immersion and the original map is separated. Only the diagonal,
   and never the original map, was required to be locally of finite type. -/
theorem separated_iff_diagonal_universallyClosed {B : Scheme.{u}}
    (U V : AlgebraicSpace B) (g : U ⟶ V) :
    MapIsSeparated g ↔
      MapIsUniversallyClosed
        (ObjectProperty.homMk (Limits.pullback.diagonal g.hom) :
          U ⟶ ⟨Limits.pullback g.hom g.hom, (fibreProduct_isAlgebraicSpace U U V g g).1⟩) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
