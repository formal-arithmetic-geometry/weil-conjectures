module

public import Sheaf.CategoryTheory.GradedSheafModule
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Functor.EpiMono

/-! # An acyclic dg hull preserves monomorphisms

Source: Stacks Project, sdga.tex, Tags 0FSK and 0FSL, as used in 0FSS;
left modules via the graded opposite algebra
(blueprint: lem-sfb-sheaf-dg-acyclic-hull).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.SheafDg

/-- The differential-forgetting functor has an acyclic left adjoint preserving monos.
Source: Stacks, sdga.tex, Tags 0FSK and 0FSL, as used in 0FSS, left convention
(blueprint: lem-sfb-sheaf-dg-acyclic-hull).

Proof plan (all steps use def-sfb-sheaf-dg-module-localization; the two-coordinate
sheaf construction and its kernels also use def-weil-sheaf-of-modules-category,
in the universes of def-weil-size-convention):
1. Set G(N)^n=N^n ⊕ N^(n-1), with componentwise restrictions and D(x,y)=(0,x).
The two sheaf conditions hold coordinatewise, and D squared is zero.
2. For a of degree p use a(x,y)=(ax-(-1)^p d(a)y,(-1)^p ay).
The Leibniz rule for d_A proves associativity by expansion; d_A(1)=0 proves
unitality. This action is coefficient-bilinear and respects restrictions.
3. Expanding both sides gives D(a(x,y))=d(a)(x,y)+(-1)^p aD(x,y).
For a graded module map u put G(u)(x,y)=(u(x),u(y)); this commutes with D
and the action and respects identities and compositions.
4. Extend a graded map f:N→F(M) to a dg map by (x,y)↦f(x)+d_M f(y).
The differential and action identities follow from d_M squared zero and Leibniz.
5. Restriction of a dg map t to (x,0) is its inverse: (x,y)=(x,0)+D(y,0).
Evaluation shows naturality in both variables, giving the stated adjunction.
6. The kernel of D in degree n consists of (0,y), exactly the image of D
in degree n-1, since D(y,0)=(0,y). These are identities of subsheaves,
so every cohomology sheaf is zero.
7. A mono u of graded module sheaves is injective on sections: its sectionwise
kernel is a graded module sheaf K, and its inclusion j satisfies uj=u0.
Cancellation gives j=0, forcing every kernel section to be zero.
8. Hence G(u) is injective on sections in both coordinates. If G(u)r=G(u)s,
cancel on each degree and each open, giving r=s. Thus G preserves monos. -/
theorem exists_acyclicHull {X : TopCat.{u}}
    (S : TopCat.Sheaf CommRingCat.{w} X)
    [EssentiallySmall.{w} (TopologicalSpace.Opens X)] (A : Algebra S) :
    ∃ G : GradedLeftModule (underlyingGradedAlgebra A) ⥤ LeftModule A,
      Nonempty (G ⊣
        (HomologicalComplex.forget (ringedSiteModules.{w} (rings S)) (.up ℤ)).mapMod A.X) ∧
      (∀ (N : GradedLeftModule (underlyingGradedAlgebra A)) (n : ℤ),
        IsZero ((cohomology A n).obj ((q A).obj (G.obj N)))) ∧
      G.PreservesMonomorphisms := by
  sorry

end CategoryTheory.SheafDg
