/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Topology.LocallyConstant.Algebra


/-!
# Degreewise exactness of locally constant cochains
Source: Stacks Project, Tag 0DVG.
(blueprint: lem-sc-locally-constant-cochains-degreewise-exact).
-/
@[expose] public section
universe u v w s
open CategoryTheory
namespace Rep
/-- Source: Stacks Project, Tag 0DVG, proof of degreewise exactness.
(blueprint: lem-sc-locally-constant-cochains-degreewise-exact).
Proof: Transport a short exact sequence across E. Its underlying sequence of
integer modules is short exact: kernels are invariant submodules and cokernels
are quotient representations. Submodules inherit open stabilizers, and the
stabilizer of a quotient class contains the open stabilizer of any lift.
The first cochain map is injective pointwise. Its image equals the kernel of
the second: choose a preimage through the first map at each value in that
kernel. For surjectivity of the second cochain map, choose a lift of each
value of a locally constant cochain through the coefficient surjection.
Postcomposition with this set-theoretic choice preserves local constancy,
since a cochain is constant on an open neighborhood of every point.
The coefficient-map formula hm and the additive equivalences e transport
these three assertions to the evaluation of S.map C in AddCommGrpCat.
Thus the resulting short complex is short exact in every degree. -/
theorem locallyConstantCochains_degreewise_exact
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (A : Type v) [Category.{w} A] [Abelian A]
    (E : A ≌ DiscreteContinuousRep.{0, u, max u s} ℤ G)
    (C : A ⥤ CochainComplex AddCommGrpCat.{max u s} ℕ)
    (e : ∀ (M : A) (n : ℕ),
      (C.obj M).X n ≃+ LocallyConstant (Fin n → G) (E.functor.obj M).obj.V)
    (hm : ∀ (M N : A) (f : M ⟶ N) (n : ℕ) (x : (C.obj M).X n) (g : Fin n → G),
      e N n (((C.map f).f n) x) g = (E.functor.map f).hom.hom (e M n x g))
    [C.Additive] :
    ∀ (S : ShortComplex A), S.ShortExact → ∀ n : ℕ,
      ((S.map C).map (HomologicalComplex.eval
        AddCommGrpCat.{max u s} (ComplexShape.up ℕ) n)).ShortExact := by sorry

end Rep
