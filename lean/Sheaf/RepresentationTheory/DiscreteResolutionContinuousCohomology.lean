/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.Grp.AB
import Sheaf.CategoryTheory.EffaceableDeltaFunctorUniversal
import Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor

/-!
# Continuous cohomology from a transported injective resolution

Source: Stacks Project, Etale Cohomology, Section 0DVG.
(blueprint: lem-sc-discrete-resolution-continuous-cohomology).
-/

@[expose] public section

universe u v w s

open CategoryTheory

namespace Rep

/-- Invariants of a transported injective resolution compute homogeneous continuous
cohomology, with all coefficient modules in the same universe.

Source: Stacks Project, Etale Cohomology, Section 0DVG, profinite comparison.
(blueprint: lem-sc-discrete-resolution-continuous-cohomology).

Proof: An equivalence of abelian categories preserves injective objects and exactness,
so E carries the given resolution to an injective resolution in discrete representations.
Continuous inhomogeneous cochains are exact on short exact sequences: a continuous map
from a compact finite power of G to a discrete module has finite image, and finitely many
lifts through a surjection give a continuous lifting. Their degree-zero cohomology is
invariants. For a discrete module M, the orbit map m maps to (x maps to x*m) embeds M
into locally constant functions G to M with right translation. Each locally constant
function has open stabilizer: compactness gives a finite clopen partition, and continuity
of multiplication gives a common open subgroup stabilizing this partition. The insertion
operator h(F)(g1,...,g(n-1))(x) = F(x,g1,...,g(n-1))(1) satisfies dh+hd=1 in positive
degrees; it is continuous by the compact-open exponential law and finite clopen partitions.
This effaces positive continuous cohomology. The cohomological delta-functor is therefore
universal, and agrees with derived invariants in degree zero; extending the identity in
both directions and using uniqueness gives inverse comparisons in every degree.
The compact-open exponential law identifies iterated maps with jointly continuous maps.
Homogeneous equivariant cochains evaluate at (1,g1,g1*g2,...) to inhomogeneous cochains;
the inverse sends c to (g0,...,gn maps to g0*c(g0^-1*g1,...,g(n-1)^-1*gn)). Expanding
alternating omission proves compatibility with the differential. Postcomposition with
the equivariant coefficient equivalence identifies the complexes for E(F) and N.
Taking kernel modulo image, which computes underlying TopModuleCat homology, completes
the comparison with the invariant complex of the given resolution. This uses integer
modules and does not require a finite coefficient ring. -/
theorem nonempty_equiv_invariantResolution_continuousCohomology
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Category.{w} A] [Abelian A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G)
    [(E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
      forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat).Additive]
    (F : A) (I : InjectiveResolution F)
    (N : TopRep.{max u s} ℤ G) [DiscreteTopology N.V]
    (e : (E.functor.obj F).obj.V ≃ₗ[ℤ] N.V)
    (he : ∀ (g : G) (x : (E.functor.obj F).obj.V),
      e ((E.functor.obj F).obj.ρ g x) = N.ρ g (e x)) (q : ℕ) :
    Nonempty (((((E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
      forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex).homology q) ≃
      continuousCohomology q N) := by
  sorry

end Rep
