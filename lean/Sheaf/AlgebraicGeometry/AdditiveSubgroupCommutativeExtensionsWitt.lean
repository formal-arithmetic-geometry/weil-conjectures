module

public import Sheaf.AlgebraicGeometry.LengthTwoWittExtensionVerschiebung
public import WeilConjectures.AlgebraicGeometry.GroupScheme.Defs
public import Mathlib.CategoryTheory.Monoidal.Grp
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.MvPolynomial.Basic
import Sheaf.AlgebraicGeometry.AdditiveSubgroupPolynomialQuotient
import Mathlib.RingTheory.AdjoinRoot
import Sheaf.RingTheory.SymmetricPolynomialCocycleNormalForm

/-! # Commutative extensions of additive subgroups are Witt pullbacks

Source: Milne, Algebraic Groups (2017), Proposition 15.27, pp. 316–317, and (113)
(blueprint: lem-sfb-additive-subgroup-commutative-extensions-witt).

The isomorphism to the scheme pullback is specified by both projections. Both components
are group homomorphisms, so it is an isomorphism for the induced pullback group law.
The kernel and quotient identifications are retained, including the split case.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.StandardGroupSchemes

/-- Every commutative extension of a closed additive subgroup by the additive group over
 a perfect field of positive characteristic is a pullback of the two-coordinate Witt
 extension, with the specified kernel and quotient unchanged.
 Source: Milne, Algebraic Groups (2017), Proposition 15.27, pp. 316–317, display (113)
 (blueprint: lem-sfb-additive-subgroup-commutative-extensions-witt).

Proof:
1. The kernel identification makes q an additive torsor: (e,t) ↦ (e,e+i(t)) is an
   isomorphism E × Gₐ → E ×_Q E, with inverse given by the unique kernel coordinate
   of e'-e. By lem-sfb-additive-affine-torsor-section it has a section s over affine Q.
   Subtract its value at zero to normalize s(0)=0. Then (t,x) ↦ i(t)+s(x) identifies
   E with Gₐ × Q, respecting the specified kernel and quotient.
2. Write s(x)+s(y)=i(f(x,y))+s(x+y). The group axioms say f is a regular normalized
   symmetric two-cocycle. These are identities of morphisms on every test algebra.
   The affine-spectrum and polynomial universal properties identify regular functions
   on Q powers with the corresponding polynomial quotient rings.
3. If Q is the entire additive line, f is already a polynomial F on that line squared.
   Otherwise lem-sfb-additive-subgroup-polynomial-quotient gives k[Q]=k[T]/(P), P monic
   of positive degree n and P(0)=0. The monic quotient basis of
   lem-weil-pbc-monic-quotient-free gives the unique lift F with both degrees below n.
   Symmetry and normalization follow by uniqueness. The cocycle defect in three
   variables has every variable degree below n and vanishes modulo the three copies
   of P. Successive monic remainders force it to vanish before reduction, even for
   nonreduced Q. Thus F is a normalized symmetric cocycle on the whole line.
4. By lem-sfb-symmetric-polynomial-cocycle-normal-form,
   F = ∑ aᵢ cₚ(X,Y)^(p^i) + δb, with b(0)=0. Perfectness gives bᵢ^p=aᵢ.
   The additive polynomial h(T)=∑ bᵢ T^(p^i) restricts to a homomorphism Q → Gₐ.
5. Add the vectors (bᵢ T^(p^i),0) using the polynomial Witt law of
   lem-sfb-length-two-witt-extension-verschiebung, obtaining (h(T),B(T)).
   Regrouping the sums at X and Y gives
   B(X)+B(Y)+cₚ(h(X),h(Y)) = B(X+Y)+∑ aᵢ cₚ(X,Y)^(p^i),
   because cₚ is homogeneous of degree p with prime-field coefficients. Hence
   F=cₚ(h(X),h(Y))+δ(b+B), and B(0)=0.
6. Put u=(b+B)|_Q. Send i(t)+s(x) to (x,(h(x),t+u(x))) in the scheme pullback.
   The preceding cocycle identity makes this a group homomorphism. Its regular
   inverse sends (x,(h(x),v)) to i(v-u(x))+s(x). The affine-spectrum and fibre-product
   universal properties give inverse scheme morphisms. Since h(0)=u(0)=0, they are
   the identity on the specified kernel and quotient. The second component a obeys
   τa=hq and ai=j. Zero coefficients allow h=0, including split extensions; no
   smoothness or connectedness assumption entered the argument. -/
theorem additive_subgroup_commutative_extensions_witt
    (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (hperfect : ∀ x : k, ∃ y : k, y ^ p = x)
    (Q E : Over (Spec (.of k))) [GrpObj Q] [GrpObj E]
    [IsCommMonObj Q] [IsCommMonObj E]
    [IsAffine Q.left] [IsAffine E.left]
    [LocallyOfFiniteType Q.hom] [QuasiCompact Q.hom]
    [LocallyOfFiniteType E.hom] [QuasiCompact E.hom]
    (ι : Q ⟶ additive k) [IsClosedSubgroupScheme ι]
    (i : additive k ⟶ E) (q : E ⟶ Q) [IsMonHom i] [IsMonHom q]
    (hkernel : ∃ e : additive k ≅ GrpObj.ker q, e.hom ≫ GrpObj.kerι q = i)
    [Flat q.left] [Surjective q.left] [LocallyOfFinitePresentation q.left]
    [QuasiCompact q.left] [QuasiSeparated q.left] :
    ∃ (h : Q ⟶ additive k) (a : E ⟶ LengthTwoWitt.scheme k p),
      IsMonHom h ∧ IsMonHom a ∧
      ∃ e : E ≅ pullback h (LengthTwoWitt.truncation k p),
        e.hom ≫ pullback.fst h (LengthTwoWitt.truncation k p) = q ∧
        e.hom ≫ pullback.snd h (LengthTwoWitt.truncation k p) = a ∧
        a ≫ LengthTwoWitt.truncation k p = q ≫ h ∧
        i ≫ a = LengthTwoWitt.inclusion k p := by
  sorry

end AlgebraicGeometry.StandardGroupSchemes
