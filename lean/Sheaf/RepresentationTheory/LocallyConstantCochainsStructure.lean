/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# Construction of locally constant inhomogeneous cochains
Source: Stacks Project, Etale Cohomology, Tag 0DVG, displayed differential.
(blueprint: lem-sc-locally-constant-cochains-structure).
-/

@[expose] public section
universe u v w s
open CategoryTheory
namespace Rep
/-- The locally constant integer cochain complex has natural additive coordinates.

Source: Stacks Project, Etale Cohomology, Tag 0DVG, displayed differential,
and the construction part of lem-sc-locally-constant-cochains-exact.
(blueprint: lem-sc-locally-constant-cochains-structure).

Proof: Take degree n to be the additive group of locally constant functions
from G^n to the carrier of E(M). Define the differential by the formula below.
The non-action faces preserve local constancy by continuous precomposition
with the projections and adjacent multiplication maps. For the action face,
fix a point (g_0,t). The cochain is constant with value m near t. On the open
coset g_0 Stab(m), the action on m is constant, so this face is locally constant.
All faces are additive in the coefficient, and so is their signed sum.
Number the action face 0, the multiplication faces 1 through n, and the final
omission face n+1. The usual face relation pairs compositions of faces in the
square of the differential, with the two signs differing by a minus sign.
For two internal faces the relation is associativity or commutation of
merges of disjoint pairs; at the first face it is the action law; at the
last face it is the compatibility of omission with the other faces.
These exhaust the pairs, so the square vanishes. At n=0 this also follows
by expanding d(g acting on m minus m) and applying the action law.
These additive maps and their square-zero relation define the complex.
Postcompose cochains with E(f). Equivariance gives commutation with the
action face, and additivity gives commutation with the signed sum, hence
these are complex morphisms. Identity and composition hold pointwise.
This defines the functor C on A; take identity additive coordinates e.
The two required equations are then the definitions of the maps and
of the differential. This construction does not assert exactness. -/
theorem exists_locallyConstantCochains_structure
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Category.{w} A] [Abelian A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G) :
    ∃ C : A ⥤ CochainComplex AddCommGrpCat.{max u s} ℕ,
      ∃ e : ∀ (M : A) (n : ℕ),
          (C.obj M).X n ≃+ LocallyConstant (Fin n → G) (E.functor.obj M).obj.V,
        (∀ (M N : A) (f : M ⟶ N) (n : ℕ) (x : (C.obj M).X n) (g : Fin n → G),
          e N n (((C.map f).f n) x) g =
            (E.functor.map f).hom.hom (e M n x g)) ∧
        (∀ (M : A) (n : ℕ) (x : (C.obj M).X n) (g : Fin (n + 1) → G),
          e M (n + 1) (((C.obj M).d n (n + 1)) x) g =
            (E.functor.obj M).obj.ρ (g 0) (e M n x (fun k ↦ g k.succ)) +
              ∑ k : Fin (n + 1),
                (-1 : ℤ) ^ (k.val + 1) • e M n x (Fin.contractNth k (· * ·) g)) := by sorry
end Rep
