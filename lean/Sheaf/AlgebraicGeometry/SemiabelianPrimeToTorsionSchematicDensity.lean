module

public import Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import WeilConjectures.AlgebraicGeometry.DensePoints
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.AlgebraicGeometry.ClosedSubschemeBaseChangeIdealImage
import Sheaf.RingTheory.ReducedIdealsZeroIntersection
import Sheaf.AlgebraicGeometry.AbelianVariety.PrimeToTorsionDense
import WeilConjectures.Mathlib.AlgebraicGeometry.Geometrically.Reduced

/-! # Schematic density of invertible torsion in a semiabelian variety

Source: Milne, Abelian Varieties, I section 10; Milne, Algebraic Groups,
Theorem 12.32 and Aside 12.51. The semiabelian schematic version is the
agent-formulated extension in the DAG.
(blueprint: lem-sfb-semiabelian-prime-to-torsion-schematic-density)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory MonObj

namespace AlgebraicGeometry

/-- A closed subscheme containing every rational point killed by a positive integer
invertible in the ground field is the whole semiabelian scheme. `IsIso i` expresses
this equality as a closed subscheme, including its scheme structure.
The morphism `(𝟙 G.X ^ n).left` is multiplication by `n` using the given group law;
`(MonObj.one (X := G.X)).left` is its identity section.

Source: Milne, Abelian Varieties, I section 10 (abelian torsion input);
Milne, Algebraic Groups, Theorem 12.32 and Aside 12.51, with the agent-formulated
semiabelian extension and schematic upgrade recorded in the DAG.
(blueprint: lem-sfb-semiabelian-prime-to-torsion-schematic-density)

Proof:
1. Apply def-sfb-semiabelian-geometric-fibres to the identity geometric point.
   Obtain an exact fppf sequence from a split torus T to G to an abelian variety B.
   The Laurent presentation makes T affine and finitely presented; lifting units
   across square-zero extensions proves smoothness (def-sbc-smooth-morphisms).
   For rank zero this is the identity scheme. Its Hopf algebra is F[Z^r].
2. The quotient q is a T-torsor: after an fppf local section s its trivialization
   sends t to s+i(t), with inverse y to i^{-1}(y-s), on every test scheme.
   Apply lem-sfb-smooth-affine-group-torsor-representability. Identify its representing
   scheme with G using lem-galois-yoneda-fully-faithful. Thus q is smooth,
   surjective and open.
3. Over a rational n-torsion point b of B the same torsor argument makes G_b smooth
   and nonempty. Algebraic closedness implies separable closedness, so
   lem-pc-rational-points-dense supplies y in G_b(F). Write ny=i(a). Coordinatewise
   n-th roots in F give t in T(F) with nt=a; then g=y-i(t) is an n-torsion lift of b.
   This also works for rank zero, with identity correction.
4. Translate T to G_b by g and pull back Z, using
   lem-pc-closed-subscheme-base-change-ideal-image. Every invertible-order torsion
   point t of T maps to an invertible-order torsion point of G, killed by nm.
   The finite reduced torus kernels in
   lem-sfb-smooth-diagonal-prime-to-characteristic-torsion-density are disjoint unions
   of Spec F, so pointwise factorization gives factorization of each kernel.
   Its schematic density clause gives the entire translated fibre contained in Z.
5. If the open complement of Z were nonempty, its image under q would be nonempty
   and open. By lem-sfb-abelian-prime-to-torsion-dense it contains an invertible-order
   torsion rational point b. Its residue field is F, and def-pc-scheme-fibre identifies
   the image of G_b with the topological fibre over b, contradicting step 4.
   Hence Z has all of G as support, including when B has dimension zero.
6. By sbc-lem-smooth-geometrically-reduced, G is reduced. On each affine open its
   ring R is reduced (def-pc-reduced-scheme), and Z is defined by an ideal I
   (def-weil-closed-immersion). Full support gives V(I)=Spec R. Apply
   lem-sc-reduced-ideals-zero-intersection with both ideals I: I=I intersect I=0.
   These affine equalities show that the given closed immersion is an isomorphism.
   The argument includes the trivial group and n=1. -/
theorem semiabelian_isIso_of_contains_primeToTorsion
    (F : Type u) [Field F] [IsAlgClosed F]
    (G : Grp (Over (Spec (.of F)))) [IsCommMonObj G.X]
    [Smooth G.X.hom] [IsSeparated G.X.hom]
    [LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]
    (hG : HasSemiabelianGeometricFibres G)
    {Z : Scheme.{u}} (i : Z ⟶ G.X.left) [IsClosedImmersion i]
    (hT : ∀ (n : ℕ), 0 < n → (n : F) ≠ 0 →
      ∀ x : G.X.hom.fieldPoints F,
        x.1 ≫ (𝟙 G.X ^ n).left = (MonObj.one (X := G.X)).left →
          ∃ z : Spec (.of F) ⟶ Z, z ≫ i = x.1) :
    IsIso i := by
  sorry

end AlgebraicGeometry
