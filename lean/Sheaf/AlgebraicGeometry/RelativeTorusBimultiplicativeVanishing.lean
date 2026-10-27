module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Sheaf.AlgebraicGeometry.RelativeSplitTorus
import Sheaf.AlgebraicGeometry.RingDiagonalizableGroup
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.RingTheory.AdjoinRoot

/-! # Vanishing of bimultiplicative pairings of relative multiplicative groups

Source: Conrad, Reductive group schemes, Proposition 4.3.1, proof, printed p.127.
(blueprint: lem-sfb-relative-torus-bimultiplicative-vanishing).

The rank-one relative split torus is the multiplicative group over the arbitrary base S.
Multiplication on Hom sets is the group law of the represented group functor.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

/-- A separately multiplicative morphism from G_m ×_S G_m to a separated commutative
S-group scheme is the identity on every test scheme.
Source: Conrad, Reductive group schemes, Proposition 4.3.1, proof, printed p.127.
(blueprint: lem-sfb-relative-torus-bimultiplicative-vanishing).

Proof:
1. On affine tests identify D_A(Z) with G_m by its unit coordinate. Apply
   lem-sfb-relative-diagonalizable-character-duality to nZ ⊆ Z: the nth-power map
   is an fppf sheaf quotient. The local-surjectivity assertion of
   lem-cbc-set-presheaf-sheafification-local-bijection gives fppf-local nth roots.
   Use def-pc-fppf-site, lem-trf-fppf-covering-is-fpqc and
   lem-weil-pbc-fpqc-representable-descent to descend equalities; affine open covers
   treat general tests, and the empty test has only one morphism.
2. Cancellation gives b(1,c)=1. If a^n=1, locally write c=d^n, and compute
   b(a,c)=b(a,d)^n=b(a^n,d)=1. Descent makes b trivial on mu_n ×_S G_m.
3. Separatedness makes the equalizer of b and the identity map a closed subscheme
   of G_m ×_S G_m, by lem-weil-pbc-closed-immersion-base-change. Over each affine
   open Spec R of the second factor its ideal I in R[t,t^-1] lies in every (t^n-1).
   This uses def-weil-closed-immersion and the affine-spectrum dictionary.
4. For f in I multiply by a power of t to obtain a polynomial g. Choose n larger
   than all exponents in g. By lem-weil-pbc-monic-quotient-free, the classes of
   1,t,...,t^(n-1) form a basis modulo t^n-1, so every coefficient of g is zero.
   Hence I=0 even for nonreduced R or R=0. The equalizer is the whole product,
   and evaluation on every test scheme proves the assertion. -/
theorem relativeTorus_bimultiplicative_eq_one
    (S : Scheme.{u}) (Z : Over S) [GrpObj Z] [IsCommMonObj Z] [IsSeparated Z.hom]
    (b : (relativeSplitTorus S 1).X ⊗ (relativeSplitTorus S 1).X ⟶ Z)
    (hleft : ∀ (T : Over S) (a a' c : T ⟶ (relativeSplitTorus S 1).X),
      lift (a * a') c ≫ b = (lift a c ≫ b) * (lift a' c ≫ b))
    (hright : ∀ (T : Over S) (a c c' : T ⟶ (relativeSplitTorus S 1).X),
      lift a (c * c') ≫ b = (lift a c ≫ b) * (lift a c' ≫ b)) :
    ∀ (T : Over S) (a c : T ⟶ (relativeSplitTorus S 1).X), lift a c ≫ b = 1 := by
  sorry

end AlgebraicGeometry
