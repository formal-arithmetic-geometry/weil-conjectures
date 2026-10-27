module

public import Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import WeilConjectures.Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Sheaf.AlgebraicGeometry.GeometricReducedFiniteTypePerfectField
import Mathlib.AlgebraicGeometry.Group.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import WeilConjectures.AlgebraicGeometry.DensePoints
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.MorphismProperty.Descent
import Mathlib.CategoryTheory.Sites.Precoverage
import Mathlib.CategoryTheory.Yoneda

/-!
# The reduced normal kernel factorization

Source: Milne, Algebraic Groups (2017), Corollary 1.39, Propositions 1.26 and 1.52,
Theorems 5.14 and 5.28, Proposition 5.29, Exercises 5-5 and 5-6;
Stacks Project, Tag 02VL
(blueprint: lem-sfb-reduced-normal-kernel-factorization).

Kernel squares specify the scheme-theoretic kernels. The isomorphism to the nilradical
subscheme identifies the reduced kernel together with its inclusion. Quotients use the
existing fppf coset-sheaf presentation, including its specified torsor isomorphism.
Actions are Mathlib module objects; multiplicativity on every test scheme says that
these group actions are by group automorphisms.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace AlgebraicGeometry

/-- A faithfully flat map of smooth connected affine groups factors by its reduced kernel.
Neither the kernel nor its reduction is assumed connected, and the kernel may be nonreduced.

Source: Milne, Algebraic Groups (2017), Corollary 1.39, Proposition 1.26, Proposition 1.52,
Theorems 5.14 and 5.28, Proposition 5.29, Exercises 5-5 and 5-6, Proposition 7.15 and
Remark 7.16; Stacks Project, Tag 02VL
(blueprint: lem-sfb-reduced-normal-kernel-factorization).

Proof plan, following the ten steps of the DAG node:
1. The kernel subgroup lemma gives N as the identity fibre of q, normal on every algebra
   of points. Its nilradical subscheme L is affine of finite type and has the same
   underlying space and dimension as N. Algebraic closedness makes k perfect.
2. Perfect-field reduced tensor products make L times L reduced. Multiplication, inverse
   and identity kill the nilradical of N and factor uniquely through L; the monic closed
   inclusion then reflects the group identities.
3. Geometric reducedness over a perfect field and the geometrically reduced group
   smoothness lemma make L smooth. Smoothness makes H reduced. Reducedness of H times L
   factors conjugation through L, proving normality without connectedness of L.
4. The affine normal quotient geometry lemma gives P, a, the fppf coset presentation and
   torsor isomorphism. Smoothness descends to P. The identity section and connectedness
   make H geometrically connected, so P is connected too.
5. The base change of a along itself is a projection from H times L, up to swapping
   projections. It is smooth. Smooth fpqc base descent (02VL) makes a smooth.
6. The faithfully flat quotient universal property identifies the given J with H/N:
   the maps in both directions are inverse by uniqueness. The same property factors q
   uniquely through a as b.
7. Nested homogeneous quotient geometry and equality of dimensions make b finite and
   faithfully flat. The fpqc uniqueness of representable descent identifies this with
   the factorization map. Inverse-image subgroup correspondence identifies ker b with
   N/L, retaining the induced map c and the equation i followed by a equals c followed
   by the kernel inclusion j.
8. Over an algebraically closed extension, the smooth surjection a has rational points
   in every fibre. Lift two points with the same b-image; their difference is in N and
   hence in L, because maps to fields kill nilpotents. The coset criterion identifies
   the points. Passing from arbitrary fields to their algebraic closures proves the
   field-point criterion for universal injectivity.
9. Equivariance preserves N. Smoothness of A makes A reduced, so A times L is reduced;
   the action into N factors through L. Inverse elements give preservation as a subgroup
   scheme after every base change.
10. Lift P-points along the fpqc covering a, act on their H-lifts, and apply a. Different
    lifts differ by L and give the same result by step 9. Representable descent glues
    uniquely, and Yoneda supplies the action morphism. Its laws and multiplicativity
    descend from H after common refinements. Both a and b are equivariant by their
    defining formulas and uniqueness of descent.
-/
theorem reduced_normal_kernel_factorization
    {k : Type u} [Field k] [IsAlgClosed k]
    (H J : Grp (Over (Spec (.of k)))) (q : H ⟶ J)
    [IsAffine H.X.left] [Smooth H.X.hom] [ConnectedSpace H.X.left]
    [LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]
    [IsAffine J.X.left] [Smooth J.X.hom] [ConnectedSpace J.X.left]
    [LocallyOfFiniteType J.X.hom] [QuasiCompact J.X.hom]
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left] :
    ∃ (N L P K : Grp (Over (Spec (.of k))))
      (i : N ⟶ H) (r : L ⟶ N) (a : H ⟶ P) (b : P ⟶ J)
      (j : K ⟶ P) (c : N ⟶ K)
      (e : L.X.left ≅ N.X.left.nilradical.subscheme),
      IsPullback i.hom.hom (toUnit N.X) q.hom.hom η[J.X] ∧
      r.hom.hom.left = e.hom ≫ N.X.left.nilradical.subschemeι ∧
      Smooth L.X.hom ∧
      IsClosedSubgroupScheme (r ≫ i).hom.hom ∧
      IsNormalSubgroupScheme (r ≫ i).hom.hom ∧
      IsAffine P.X.left ∧ Smooth P.X.hom ∧ ConnectedSpace P.X.left ∧
      LocallyOfFiniteType P.X.hom ∧ QuasiCompact P.X.hom ∧
      IsFppfGroupQuotient (r ≫ i) a ∧
      Smooth a.hom.hom.left ∧ Flat a.hom.hom.left ∧ Surjective a.hom.hom.left ∧
      LocallyOfFinitePresentation a.hom.hom.left ∧
      QuasiCompact a.hom.hom.left ∧ QuasiSeparated a.hom.hom.left ∧
      IsFinite b.hom.hom.left ∧ Flat b.hom.hom.left ∧ Surjective b.hom.hom.left ∧
      UniversallyInjective b.hom.hom.left ∧ a ≫ b = q ∧
      IsPullback j.hom.hom (toUnit K.X) b.hom.hom η[J.X] ∧
      IsFppfGroupQuotient r c ∧ i ≫ a = c ≫ j ∧
      (∀ (A : Grp (Over (Spec (.of k))))
        [IsAffine A.X.left] [Smooth A.X.hom] [ConnectedSpace A.X.left]
        [LocallyOfFiniteType A.X.hom] [QuasiCompact A.X.hom]
        (_ : ModObj A.X H.X) (_ : ModObj A.X J.X),
        (∀ (T : Over (Spec (.of k))) (t : T ⟶ A.X) (x y : T ⟶ H.X),
          t • (x * y) = (t • x) * (t • y)) →
        (∀ (T : Over (Spec (.of k))) (t : T ⟶ A.X) (x y : T ⟶ J.X),
          t • (x * y) = (t • x) * (t • y)) →
        IsModHom A.X q.hom.hom →
        ∃ (_ : ModObj A.X L.X) (_ : ModObj A.X P.X),
          (∀ (T : Over (Spec (.of k))) (t : T ⟶ A.X) (x y : T ⟶ L.X),
            t • (x * y) = (t • x) * (t • y)) ∧
          (∀ (T : Over (Spec (.of k))) (t : T ⟶ A.X) (x y : T ⟶ P.X),
            t • (x * y) = (t • x) * (t • y)) ∧
          IsModHom A.X (r ≫ i).hom.hom ∧
          IsModHom A.X a.hom.hom ∧ IsModHom A.X b.hom.hom) := by
  sorry

end AlgebraicGeometry
