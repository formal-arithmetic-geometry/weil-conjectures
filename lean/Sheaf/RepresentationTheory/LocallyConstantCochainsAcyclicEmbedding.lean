/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected


/-!
# LocallyConstantCochainsAcyclicEmbedding

Source: Stacks Project, Etale Cohomology, Tag 0DVG.
(blueprint: lem-sc-locally-constant-cochains-acyclic-embedding).
-/

@[expose] public section

universe u v w s

open CategoryTheory

namespace Rep

/-- Every object embeds in one whose locally constant integer cochain complex is
exact in all positive degrees.

Source: Stacks Project, Etale Cohomology, Tag 0DVG, final profinite comparison;
step 4 of lem-sc-locally-constant-cochains-effaceable (agent-supplied contraction).

Proof: Construct D(E(M)) as LC(G,E(M)) with pointwise integer module structure and
right translation rho(h)f(x)=f(x*h). Every function has a finite clopen partition.
Compactness and continuity of multiplication give a common identity neighborhood
preserving that partition under right translation. A compact Hausdorff totally
disconnected group has an open subgroup inside that neighborhood. Thus stabilizers
are open and D(E(M)) is a discrete representation. The orbit map m to (x to rho(x)m)
is locally constant, integer-linear and equivariant; evaluation at 1 is its left
inverse, so it is monic. Take N=E.inverse.obj D(E(M)) and transport the orbit map via
the unit and counit of E. These are specified constructions, not arbitrary existence
choices. Transport the coordinates of C(N) through the counit to cochains with values
in LC(G,E(M)). For a degree n+1 cochain F put h_n(F)(g)(x)=F(x,g)(1).
This is locally constant in x. For local constancy in g with the whole function of x
fixed, cover the compact x factor by finitely many product neighborhoods on which F
is constant and intersect their g neighborhoods. The contraction is additive.
Expand d_n h_n F and h_(n+1) d_(n+1) F at g,x using the differential equation.
The action face uses right translation. Their sum is F(g)(x): the merged first face
cancels the extra translation term, each interior merged face cancels with the
opposite sign, and the final deletion terms cancel. This includes n=0.
Consequently every positive-degree cocycle F is d(h(F)), and conversely every boundary
is a cocycle. The coordinate equivalences transport this equality of kernel and image
to exactness of C(N) in every positive degree. The coefficient equation identifies
transport under the counit. The orbit map remains monic under the equivalence.
(blueprint: lem-sc-locally-constant-cochains-acyclic-embedding). -/
theorem locallyConstantCochains_acyclic_embedding
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (A : Type v) [Category.{w} A] [Abelian A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G)
    (C : A ⥤ CochainComplex AddCommGrpCat.{max u s} ℕ)
    (e : ∀ (M : A) (n : ℕ),
      (C.obj M).X n ≃+ LocallyConstant (Fin n → G) (E.functor.obj M).obj.V)
    (hm : ∀ (M N : A) (f : M ⟶ N) (n : ℕ) (x : (C.obj M).X n) (g : Fin n → G),
      e N n (((C.map f).f n) x) g = (E.functor.map f).hom.hom (e M n x g))
    (hd : ∀ (M : A) (n : ℕ) (x : (C.obj M).X n) (g : Fin (n + 1) → G),
      e M (n + 1) (((C.obj M).d n (n + 1)) x) g =
        (E.functor.obj M).obj.ρ (g 0) (e M n x (fun k ↦ g k.succ)) +
          ∑ k : Fin (n + 1),
            (-1 : ℤ) ^ (k.val + 1) • e M n x (Fin.contractNth k (· * ·) g))
    (M : A) : ∃ (N : A) (f : M ⟶ N), Mono f ∧
      ∀ n : ℕ, 0 < n → (C.obj N).ExactAt n := by sorry

end Rep
