/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q10
-/
module

public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

import Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints
import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-! # Projective immersions of affine homogeneous quotients

Source: Milne, Algebraic Groups (2017), Theorem 7.18 and its proof, p.143,
using Theorem 4.27, pp.94--95, and Proposition 7.17, p.143; Theorem 8.43, p.161.
(blueprint: lem-sfb-affine-homogeneous-quotient-projective-immersion)

The Cartesian square in the hypothesis says both that the quotient map is right
H-invariant and that its kernel pair is exactly `(g,h) ↦ (g,gh)`.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits CartesianMonoidalCategory
open scoped MonObj

namespace AlgebraicGeometry

/-- A represented quotient of a smooth affine finite-type group by any closed
subgroup admits an immersion into a projective space over the original field.

Source: Milne, Algebraic Groups (2017), Theorem 7.18 and its proof, p.143,
Theorem 4.27, pp.94--95, Proposition 7.17, p.143, and Theorem 8.43, p.161.
(blueprint: lem-sfb-affine-homogeneous-quotient-projective-immersion)

Proof (the six steps of the node):
1. Apply lem-sfb-chevalley-scheme-line-stabilizer to obtain a nonzero finite
   representation E and a line D with scheme-theoretic stabilizer H, on every
   test algebra. Choose a basis and set N = dim(E) - 1.
2. The projective-space functor-of-points theorem identifies points with locally
   direct-summand lines, by dualizing the universal invertible quotient. The
   representation therefore gives a natural projective action; Yoneda makes it
   an action morphism. The line D gives a rational point x whose stabilizer is H.
   Check this also on arbitrary test schemes by an affine open cover.
3. Projective space is proper, hence separated and finite type. Apply
   lem-sfb-smooth-rational-orbit-arbitrary-field to obtain its locally closed
   orbit O and a flat surjective locally finitely presented orbit map G → O.
4. The kernel pair of the orbit map is G × H: the inverse to (g,h) ↦ (g,gh)
   is (g,g') ↦ (g,g⁻¹g'). The stabilizer equality ensures that g⁻¹g' belongs
   to H. Yoneda and the fibre-product universal property give the isomorphism.
5. Both maps from G are fppf covers, hence fpqc covers. Representable fpqc
   descent gives maps Y → O and O → Y from their identical kernel pairs.
   Uniqueness after either cover proves that they are inverse and over k.
6. Compose Y ≅ O with the orbit immersion. In its closed-then-open
   factorization, precomposition with an isomorphism preserves the closed
   immersion. If H = G, the orbit is the rational point x, and the same
   argument includes G = 1. No smoothness or normality of H is needed.
-/
theorem exists_projectiveSpace_immersion_of_affine_homogeneous_quotient
    {k : Type u} [Field k]
    (G H : Over (Spec (.of k))) [GrpObj G] [GrpObj H]
    [IsAffine G.left] [LocallyOfFiniteType G.hom] [QuasiCompact G.hom]
    [Smooth G.hom] (i : H ⟶ G) [IsClosedSubgroupScheme i]
    (Y : Over (Spec (.of k)))
    [IsSeparated Y.hom] [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]
    (q : G ⟶ Y) [Flat q.left] [Surjective q.left]
    [LocallyOfFinitePresentation q.left] [QuasiCompact q.left] [QuasiSeparated q.left]
    (hq : IsPullback (fst G H) (fst G H * (snd G H ≫ i)) q q) :
    ∃ (N : ℕ) (j : Y.left ⟶ ProjectiveSpace (ULift.{u} (Fin (N + 1))) (Spec (.of k))),
      IsImmersion j ∧
        j ≫ (ProjectiveSpace (ULift.{u} (Fin (N + 1))) (Spec (.of k)) ↘ Spec (.of k)) =
          Y.hom := by
  sorry

end AlgebraicGeometry
