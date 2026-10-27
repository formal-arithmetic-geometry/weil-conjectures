/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q118
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Smooth.Basic
public import WeilConjectures.RingTheory.GRing
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Sheaf.FieldTheory.SeparatingTranscendenceBasisFiniteSubextension
import WeilConjectures.AlgebraicGeometry.SpreadFiniteSeparableExtension
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.EtaleSmoothZeroDimensionalFibres
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.DedekindDomain.Basic

/-!
# Smooth coefficient systems in characteristic zero

Source: Bierstone--Milman--Temkin, Q-universal Desingularization, Theorem 7.5(1),
Definition 7.2 and Remark 7.3(1), field case; Stacks, Definitions 0382 and 07BZ
(blueprint: lem-per-char-zero-smooth-coefficient-system).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace FieldTheory

/-- The ring diagram of an ordered family of rational subalgebras, with its canonical
inclusion maps. Source: BMT, Theorem 7.5(1), field case
(blueprint: lem-per-char-zero-smooth-coefficient-system). -/
def coefficientSubalgebraDiagram {k : Type u} [Field k] [CharZero k]
    {D : Type u} [PartialOrder D] (R : D → Subalgebra ℚ k) (hR : Monotone R) :
    D ⥤ CommRingCat.{u} where
  obj i := CommRingCat.of (R i)
  map f := CommRingCat.ofHom (Subalgebra.inclusion (hR (leOfHom f))).toRingHom
  map_id := by intros; ext; rfl
  map_comp := by intros; ext; rfl

/-- The canonical cocone of inclusions of the coefficient subalgebras into their field.
Source: BMT, Theorem 7.5(1), field case
(blueprint: lem-per-char-zero-smooth-coefficient-system). -/
def coefficientSubalgebraCocone {k : Type u} [Field k] [CharZero k]
    {D : Type u} [PartialOrder D] (R : D → Subalgebra ℚ k) (hR : Monotone R) :
    Cocone (coefficientSubalgebraDiagram R hR) where
  pt := CommRingCat.of k
  ι :=
    { app := fun i ↦ CommRingCat.ofHom (R i).val.toRingHom
      naturality := by intros; ext; rfl }

/-- A characteristic-zero field admits a small nonempty directed coefficient system of
finite-type smooth rational subalgebras, with smooth transition inclusions, union the field,
its canonical ring-colimit cocone, and regular inclusions into the field.
Source: BMT, Theorem 7.5(1), Definition 7.2 and Remark 7.3(1), field case
(blueprint: lem-per-char-zero-smooth-coefficient-system).

Proof (the explicit construction in the DAG):
1. Identify \mathbf Q with its prime subfield in k. By [lem-exc-transcendence-basis-exists],
   choose a transcendence basis B\subseteq k over \mathbf Q [def-weil-pbc-transcendence-basis].
   Put A_T=\mathbf Q[t\mid t\in T]\subseteq k and F_T=\mathbf Q(T)=\operatorname{Frac}(A_T) for
   each finite T\subseteq B. Algebraic independence identifies A_T with a polynomial ring. The
   extension k/\mathbf Q(B) is algebraic and separable: an irreducible polynomial in
   characteristic zero has nonzero derivative of smaller degree, hence is relatively prime to its
   derivative. This also proves separability for every algebraic extension of any F_T used below.

2. Given a finite subset S\subseteq k and a prescribed finite T_0\subseteq B,
   [lem-weil-pbc-separating-transcendence-basis-finite-subextension] supplies a finite T\subseteq
   B such that F_T(S)/F_T is finite separable. Replace T by U=T\cup T_0. The same finitely many
   elements of S are algebraic over F_U: their polynomials over F_T remain nonzero over F_U.
   Successively adjoining these elements gives a finite-dimensional extension L=F_U(S) of F_U
   (products of the bounded powers of the generators span it). Its separability follows from the
   characteristic-zero derivative argument in Step 1. Thus the finite-subextension conclusion can
   always be arranged with U\supseteq T_0.

3. The polynomial domain A_U is Noetherian by [lem-weil-pbc-finite-type-algebra-noetherian], since
   \mathbf Q has only the ideals 0 and \mathbf Q. Apply
   [lem-weil-pbc-spread-finite-separable-extension] to A_U, its fraction field F_U, and the finite
   separable extension L of Step 2. Obtain 0\ne c\in A_U and a domain C, finite etale over
   A_U[1/c], with its specified fraction-field identification \operatorname{Frac}(C)=L. Use this
   identification to regard C as a subring of L\subseteq k. Write each s\in S as a_s/b_s with
   a_s,b_s\in C and b_s\ne0, and put b=\prod_{s\in S}b_s (the empty product is 1). Then
   R=C[1/b]\subseteq k contains S, since a_s/b_s=a_s\prod_{s'\ne s}b_{s'}/b. By
   [lem-weil-pbc-etale-algebra-finite-presentation-localization], R is etale over A_U[1/c]. The
   identity of A_U is etale: take the monic polynomial Q(Z)=Z in
   [lem-weil-pbc-standard-etale-monic-derivative], whose algebra is A_U[Z,Y]/(Z,Y-1)=A_U. The
   localization clause of [lem-weil-pbc-etale-algebra-finite-presentation-localization] applied to
   this identity makes A_U\to A_U[1/c] etale. Composition
   [lem-weil-pbc-etale-composition-cancellation] shows
   \operatorname{Spec}R\to\operatorname{Spec}A_U is etale. We have proved: every finite S is
   contained in such an R, with U containing any prescribed T_0.

4. Let D be the set of pairs (T,R) where T\subseteq B is finite, R\subseteq k is a subring
   containing A_T, and \operatorname{Spec}R\to\operatorname{Spec}A_T is etale. Order it by
   (T,R)\leq(U,R') if T\subseteq U and R\subseteq R'. This is a partial order: reflexivity and
   transitivity are those of inclusion; mutual inequalities force equality of both components. It
   is small because it is a subset of the product of the finite subsets of B with the set of
   subrings of k. It is nonempty by Step 3 with S=T_0=\varnothing. Each A_T\to R is smooth by
   [lem-weil-pbc-etale-smooth-zero-dimensional-fibres] and
   [lem-weil-pbc-smooth-ring-map-iff-smooth-affine]. Compose it with the smooth polynomial map
   \mathbf Q\to A_T of [lem-weil-pbc-polynomial-ring-smooth], using
   [lem-weil-pbc-smooth-ring-map-base-change-composition]. Thus R is smooth over \mathbf Q, and in
   particular finitely presented and of finite type by [def-weil-pbc-smooth-ring-map].

5. Fix (T,R)\in D and a finite U\supseteq T in B. The prime 0\subset R contracts to 0\subset A_T
   since both are subrings of k. Apply [lem-weil-pbc-etale-algebra-residue-field-separable] at
   this prime: E=\operatorname{Frac}(R) is finite separable, in particular algebraic, over F_T.
   The elements of U\setminus T are algebraically independent over F_T: a polynomial relation with
   rational-function coefficients in T becomes a nonzero polynomial relation among the distinct
   elements of U after multiplying by a common nonzero denominator in A_T, contrary to
   independence of B. By [lem-zl-independence-algebraic-base] they remain independent over E,
   hence over its subring R. Consequently the subring R[U\setminus T]\subseteq k is the polynomial
   ring over R on these variables. It is also the base change A_U\otimes_{A_T}R: the homomorphism
   sends p\otimes r to pr; the inverse writes a polynomial uniquely as a sum of monomials in
   U\setminus T with coefficients in R, sending each term rM to M\otimes r. Thus
   [lem-weil-pbc-etale-ring-base-change] makes this subring etale over A_U.

6. For (T,R)\leq(U,R'), the intermediate ring P=R[U\setminus T] of Step 5 lies in R', since
   R'\supseteq R and R'\supseteq A_U. Both P and R' are etale over A_U. The map
   \operatorname{Spec}R'\to\operatorname{Spec}P commutes with their maps to
   \operatorname{Spec}A_U, so [lem-weil-pbc-etale-composition-cancellation](3) makes it etale. By
   [lem-weil-pbc-etale-smooth-zero-dimensional-fibres] and
   [lem-weil-pbc-smooth-ring-map-iff-smooth-affine], P\to R' is smooth. The map R\to P is a finite
   polynomial extension by Step 5, hence smooth by [lem-weil-pbc-polynomial-ring-smooth].
   Composition [lem-weil-pbc-smooth-ring-map-base-change-composition] proves that the transition
   inclusion R\to R' is smooth. This argument applies to our componentwise order on pairs, and
   makes no assertion about arbitrary inclusions between smooth rational subalgebras.

7. For (T,R),(T',R')\in D, choose finite lists of \mathbf Q-algebra generators of R and R', which
   exist by Step 4. Apply Step 3 to the union S of these lists and to T_0=T\cup T'. It gives
   (U,R'')\in D with U\supseteq T\cup T' and S\subseteq R''. Since R'' contains \mathbf Q and both
   generating lists, it contains both R and R'. Thus (U,R'') is an upper bound in the specified
   order. Together with nonemptiness this proves directedness. Apply Step 3 also to S=\{x\} for
   each x\in k to obtain \bigcup_{(T,R)\in D}R=k.

8. The inclusions form a ring cocone with vertex k. Given compatible ring homomorphisms h_i:R_i\to
   H, define h:k\to H by h(x)=h_i(x) at any stage containing x. If two stages contain x, a common
   upper bound and compatibility give the same value, so h is well defined. For x,y\in k, put
   their stages in a common upper stage; the ring-map identities there give h(x+y)=h(x)+h(y),
   h(xy)=h(x)h(y), and preservation of 0,1. Its restrictions are the h_i, and coverage makes it
   unique. This is precisely the ring colimit universal property of
   [def-weil-pbc-category-colimit]. For any fixed index i, the tail \{j\mid i\leq j\} still covers
   k: put i and a stage containing x into a common upper bound. The same argument gives k as the
   colimit of this tail in commutative R_i-algebras, since the unique assembled ring map respects
   the specified map out of R_i.

9. Fix i and write R=R_i\subseteq k, a domain with fraction field
   E=\operatorname{Frac}(R)\subseteq k. Flatness: the only prime of k is 0, its contraction to R
   is 0, and the induced localization map is R_{(0)}=E\to k_{(0)}=k. It is flat by
   [lem-weil-pbc-module-over-field-flat], since k is an E-vector space, so R\to k is flat by
   [lem-weil-pbc-flat-map-local-criterion]. Fibres: let \mathfrak p\subset R be prime. If
   \mathfrak p\ne0, choose 0\ne a\in\mathfrak p. In k\otimes_R\kappa(\mathfrak p) one has
   1\otimes1=a^{-1}a\otimes1=a^{-1}\otimes\bar a=0, so this fibre is the zero ring. If \mathfrak
   p=0, then \kappa(0)=E and the fibre is k: the map x\otimes(r/s)\mapsto xr/s has inverse
   x\mapsto x\otimes1, and the second composite is the identity because every nonzero s\in R is
   already invertible in k. Both fibres are Noetherian: the zero ring has one ideal, and a field
   has only 0 and the unit ideal. Geometric regularity: \kappa(\mathfrak p) has characteristic 0,
   so by [def-weil-pbc-finite-purely-inseparable-extension] its only finite purely inseparable
   extension is \kappa(\mathfrak p) itself. It remains to show that each fibre is a regular ring.
   The zero ring is Noetherian and has no prime ideals, so it is vacuously regular. The field k is
   regular by [lem-weil-pbc-field-regular-ring]. Hence R_i\to k is regular in the sense of
   [def-weil-pbc-g-ring], for every i, and all clauses are proved.
-/
theorem exists_charZero_smooth_coefficient_system (k : Type u) [Field k] [CharZero k] :
    ∃ (D : Type u) (_ : PartialOrder D),
      Nonempty D ∧ IsDirected D (· ≤ ·) ∧
      ∃ (R : D → Subalgebra ℚ k) (hR : Monotone R),
        (∀ i : D, RingHom.FiniteType (algebraMap ℚ (R i)) ∧ Algebra.Smooth ℚ (R i)) ∧
        (∀ (i j : D) (h : i ≤ j),
          @Algebra.Smooth (R i) _ (R j) _
            (Subalgebra.inclusion (hR h)).toRingHom.toAlgebra) ∧
        (∀ x : k, ∃ i : D, x ∈ R i) ∧
        Nonempty (IsColimit (coefficientSubalgebraCocone R hR)) ∧
        (∀ i : D, RingHom.IsRegular (R i).val.toRingHom) := by
  sorry

end FieldTheory
