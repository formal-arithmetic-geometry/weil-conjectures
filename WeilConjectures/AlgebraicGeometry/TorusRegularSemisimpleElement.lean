/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ReductiveTorusCentralizerTerminology
public import WeilConjectures.AlgebraicGeometry.SemisimpleGroupSchemePoint
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! # One torus element detects the scheme-theoretic centralizer

Source: Milne, Algebraic Groups (2017), Lemma 16.42, printed p.339
(blueprint: lem-sfb-torus-regular-semisimple-element).

The centralizer condition is tested after every algebra extension, including nonreduced
algebras, using the existing functor-of-points centralizer predicate.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped MonObj

namespace AlgebraicGeometry

/-- A torus in a smooth connected affine group of finite type over an algebraically closed
field contains a semisimple point whose centralizer agrees with that of the torus on all
test algebras. Source: Milne, Algebraic Groups (2017), Lemma 16.42, printed p.339
(blueprint: lem-sfb-torus-regular-semisimple-element).

Proof:
1. Apply lem-sc-kernel-subgroup to the identity of G. The kernel is the normal identity
   subgroup. By lem-sfb-normal-subgroup-representation-kernel, choose a finite-dimensional
   representation with trivial scheme kernel, hence injective on points over every algebra.
2. By lem-sfb-split-torus-representation-weight-decomposition, its restriction to T has a
   finite weight decomposition. In a concatenated weight basis, every torus point acts by
   scalar blocks over every algebra.
3. By lem-sfb-torus-finite-character-separation choose s in T(k) separating these weights.
   The weight decomposition applied to every other representation shows s is semisimple,
   including in the zero-dimensional representation.
4. If g commutes with s over A, its off-diagonal weight blocks multiplied by the differences
   of the distinct eigenvalues vanish. Those differences are nonzero in k, hence units in
   A, so the off-diagonal blocks vanish. They remain zero over every A-algebra B. The
   remaining blocks commute with the scalar blocks of every t in T(B). Injectivity of the
   faithful representation gives commutation in G(B). This includes zero rings and
   nonreduced algebras, and uses the matrix interpretation of def-sc-general-linear-group.
5. Conversely take B = A and t = s_A in the universal centralizer condition. For rank zero
   the identity point works. The chosen s precedes, and is independent of, A and g. -/
theorem torus_exists_semisimplePoint_centralizer {k : Type u} [Field k] [IsAlgClosed k]
    (G T : Grp (Over (Spec (.of k))))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    [IsAffine T.X.left] [LocallyOfFiniteType T.X.hom] [QuasiCompact T.X.hom]
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (i : T ⟶ G) (hi : IsClosedSubgroupScheme i.hom.hom)
    (hT : ∃ r : ℕ, Nonempty (T ≅ MultiplicativeType.splitTorus k r)) :
    ∃ s : StandardGroupSchemes.affine k k ⟶ T.X,
      IsSemisimpleGroupSchemePoint G.X (s ≫ i.hom.hom) ∧
      ∀ (A : Type u) [CommRing A] [Algebra k A]
        (g : StandardGroupSchemes.affine k A ⟶ G.X),
        Commute g (StandardGroupSchemes.map k (Algebra.ofId k A) ≫ s ≫ i.hom.hom) ↔
          g ∈ ReductiveTorusCentralizer.centralizerPoints i A := by
  sorry

end AlgebraicGeometry
