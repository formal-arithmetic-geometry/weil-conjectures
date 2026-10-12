/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected
import Sheaf.CategoryTheory.DeltaFunctor
import Sheaf.CategoryTheory.EffaceableDeltaFunctorUniversal
import Sheaf.CategoryTheory.RightDerivedUniversalDeltaFunctor

/-!
# Injective resolutions and locally constant inhomogeneous cochains

Source: Stacks Project, Etale Cohomology, Tag 0DVG,
section-continuous-group-cohomology, profinite comparison.
(blueprint: lem-sc-discrete-resolution-inhomogeneous-cohomology).
-/

@[expose] public section

universe u v w s

open CategoryTheory

namespace Rep

/-- Any complex with the locally constant inhomogeneous terms and differential computes
invariants of an injective resolution transported through an abelian equivalence.

Source: Stacks Project, Etale Cohomology, Tag 0DVG,
section-continuous-group-cohomology, final profinite comparison.
(blueprint: lem-sc-discrete-resolution-inhomogeneous-cohomology).

Proof: On discrete integer representations construct the functorial complex whose degree
n is the abelian group of locally constant maps G^n to the coefficient module, with the
inhomogeneous differential displayed below. The differential squares to zero by cancellation
of the face maps. Surjections of coefficients induce surjections on terms: a locally
constant map on the compact space G^n has finite image, and choosing lifts of its finitely
many values preserves local constancy. Kernels are computed pointwise, so short exact
sequences give short exact sequences of complexes. The homology long exact sequence is
natural and gives a cohomological delta-functor. Its degree zero is invariants since the
first differential is g acting on m minus m.
Embed M into locally constant maps G to M by m mapping to the orbit function x acting on m,
with right translation action on the functions. Every such function has an open stabilizer:
its finite clopen partition has a common stabilizing open subgroup, by compactness and
continuity of multiplication. For this coinduced module the insertion operator on
inhomogeneous cochains, h(F)(g1,...,g(n-1))(x) = F(x,g1,...,g(n-1))(1), is locally
constant and satisfies dh+hd=1 in positive degrees, by expansion of the differential.
Thus the delta-functor is effaceable. Equivalences preserve injectives and exactness, so
transporting resolutions across E gives derived invariants on the original category.
The discrete representation category is abelian: kernels and cokernels are the underlying
module kernels and cokernels, and open stabilizers pass to subobjects and quotients.
It has enough injectives even over the integers. Embed the underlying abelian group of M
into an injective abelian group J; locally constant maps G to J with right translation
are right adjoint to the exact forgetful functor and hence injective. The map sending m
to (g mapping to the image of g acting on m in J) is an equivariant monomorphism.
Transport these injectives and resolutions along E.
Universality of the two effaceable delta-functors and their degree-zero identification
give inverse comparisons in all degrees. No global choice of a resolution in the original
category is needed: compare the given resolution with one transported from the discrete
category, using the comparison theorem and its homotopy uniqueness. Finally t identifies
K termwise with the constructed complex. The differential equation gives a complex
isomorphism; transport homology along it. This proof uses arbitrary integer modules,
not a finite scalar ring. In degree zero there are no incoming boundaries. -/
theorem nonempty_equiv_invariantResolution_inhomogeneous
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Category.{w} A] [Abelian A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G)
    [(E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
      forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat).Additive]
    (F : A) (I : InjectiveResolution F)
    (K : CochainComplex AddCommGrpCat.{max u s} ℕ)
    (t : ∀ n : ℕ, K.X n ≃+ LocallyConstant (Fin n → G) (E.functor.obj F).obj.V)
    (ht : ∀ (n : ℕ) (x : K.X n) (g : Fin (n + 1) → G),
      t (n + 1) ((K.d n (n + 1)) x) g =
        (E.functor.obj F).obj.ρ (g 0) (t n x (fun k ↦ g k.succ)) +
          ∑ k : Fin (n + 1),
            (-1 : ℤ) ^ (k.val + 1) • t n x (Fin.contractNth k (· * ·) g))
    (q : ℕ) :
    Nonempty (((((E.functor ⋙ ObjectProperty.ι _ ⋙ Rep.invariantsFunctor ℤ G ⋙
      forget₂ (ModuleCat.{max u s} ℤ) AddCommGrpCat).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj I.cocomplex).homology q) ≃ K.homology q) := by sorry

end Rep
