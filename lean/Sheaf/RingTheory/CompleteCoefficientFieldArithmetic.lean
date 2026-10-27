module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.RationalRoot
import WeilConjectures.RingTheory.NagataOfCompleteLocal
import WeilConjectures.RingTheory.NagataRing
import WeilConjectures.RingTheory.JapaneseDomain
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.RingTheory.FiniteOverCompleteLocalProduct
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Sheaf.LinearAlgebra.FiniteTorsionFreeEmbedding
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Category.ModuleCat.Free
import WeilConjectures.RingTheory.ExistsCoefficientSubring
import WeilConjectures.RingTheory.PowerSeriesAdicEvaluation
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.FieldTheory.PurelyInseparable.Basic
import WeilConjectures.FieldTheory.PurelyInseparablePthRootTower
import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
import Mathlib.FieldTheory.Normal.Closure
import WeilConjectures.FieldTheory.FiniteGaloisReceivingSeparableExtensions
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.SeparableClosure

/-! # Complete coefficient field arithmetic

Source: literature/stacks-project/more-algebra.tex, Tags 09F8 and 09F9,
`lemma-special-case` and `theorem-epp`.
(blueprint: lem-sfb-epp-complete-coefficient-field-arithmetic)
-/

@[expose] public section

universe u v w

namespace IsDiscreteValuationRing

/-- Finite coefficient extensions over a complete DVR with algebraically closed residue field.
The residue field is represented by `IsLocalRing.ResidueField A`. The existential local-ring
and local-map witnesses make its canonical map to the residue field of the integral closure
well typed; they are conclusions, not additional assumptions. The normal overfield contains
`E` by its compatible algebra structure. The last clause uses the compositum inside `E`.

Source: literature/stacks-project/more-algebra.tex, Tag 09F8, `lemma-special-case`,
omitted normal-closure argument, and Tag 09F9, `theorem-epp`, the `k((t))` compositum paragraph.
(blueprint: lem-sfb-epp-complete-coefficient-field-arithmetic)

Proof:
1. Put C=A_E. A DVR is a principal ideal domain [def-sc-discrete-valuation-ring], so A is
   Noetherian by lem-weil-pbc-pid-noetherian-normal; being local and complete, A is a Nagata ring
   by lem-weil-pbc-complete-local-nagata. Applying def-weil-pbc-nagata-ring to the prime (0) shows
   that A=A/(0) is N-2, so def-weil-pbc-japanese-domain, applied to the finite extension E/K,
   makes C a finite A-module; no separability of E/K is used. By lem-weil-pbc-integral-closure-
   finite-extension-normal, C is a domain with fraction field E. The domain clause of lem-weil-
   pbc-finite-over-complete-local-product then says that C is a Noetherian local ring, complete
   for its maximal ideal m_C, and m_C is the only prime of C whose inverse image in A is m_A; in
   particular m_C contracts to m_A. Since dim A=1 by lem-sc-dvr-dimension-one, lem-sfb-finite-
   normalization-local-dvr applies with D=A, L=E and q=m_C: the subring {c/s : c,s in C, s not in
   m_C} of E is a DVR with fraction field E. As C is local, every s outside m_C is a unit of C, so
   this subring is C itself. Thus C is a complete DVR with fraction field E, finite over A, and A
   -> C is local. Hence k maps injectively into l=C/m_C; a finite list of A-module generators of C
   maps to a spanning list for l over k. Apply lem-weil-pbc-alg-closed-finite-extension-trivial to
   this finite field extension: the specified residue map k -> l is an isomorphism.

2. Choose uniformizers pi of A and z of C. The DVR unit-times-power lemma applied to the nonzero
   nonunit pi in C gives pi=v z^e for a unit v and e>=1. The finite A-module C is torsion free
   since C is a subring of E. Embed it in A^a by lem-per-finite-torsion-free-free-embedding; a DVR
   is a PID, so lem-weil-pbc-pid-submodule-finite-basis gives an A-basis b_1,...,b_d of C
   (transport the basis of its image back along the embedding). Reducing its unique coordinate
   expressions modulo pi gives a k-basis of C/pi C of size d.

3. The b_i are also a K-basis of E. Indeed, each x in E is c/a with c,a in C and a nonzero. Write
   a=w z^j. Choosing h with eh>=j shows pi^h/a in C and therefore x in C[1/pi]. Thus E=C[1/pi].
   Clearing powers of pi in a K-linear relation proves independence of the b_i, while localizing
   their A-linear expansions proves spanning. Consequently d=[E:K].

4. Since pi C=z^e C, filter C/pi C by the images of z^i C for 0<=i<=e. Multiplication by z^i
   identifies C/z C with z^i C/z^(i+1) C: surjectivity is the definition of the principal ideal,
   and cancellation in the domain C gives its kernel z C. This is k-linear using the residue map
   of step 1, so every successive quotient has dimension one over k. All filtered terms are
   subspaces or quotients of the finite-dimensional C/pi C. Repeatedly apply lem-trf-finite-
   dimensional-short-exact-dimension to the inclusions of successive filtered terms and their
   quotient maps. It gives dim_k C/pi C=e. Steps 2 and 3 therefore give e=d=[E:K] and m_A
   C=m_C^[E:K].

5. For the remaining equal-characteristic assertion assume char K=p, so char A=p. Apply lem-weil-
   pbc-cohen-coefficient-ring-exists to A. Its coefficient subring Lambda satisfies Lambda
   intersect m_A=p Lambda=0 and maps isomorphically onto k. The inverse of this residue
   isomorphism gives a ring section s:k -> A. Fix the uniformizer t specified in the statement.
   Since A is complete for (t), lem-weil-pbc-power-series-adic-evaluation defines evaluation
   k[[T]] -> A with coefficients mapped by s and T mapped to t.

6. Every a in A has a unique expansion sum_(i>=0) s(c_i)t^i. Construct c_0 as its residue, replace
   a by (a-s(c_0))/t in A, and repeat. For every N this recursion gives the required expansion
   modulo t^N; completeness and the evaluation formula of step 5 give the equality. For
   uniqueness, the first nonzero coefficient of a difference is a unit times its power of t: after
   removing that power, the remaining series has nonzero residue. This proves injectivity as well
   as surjectivity of the evaluation. Since every fraction in K becomes an element of A after
   multiplication by a power of t (the DVR unit-times-power lemma), the same argument gives unique
   Laurent expansions with only finitely many negative exponents.

7. The field k is perfect: a root of X^p-c exists for every c in k, and it is unique since a field
   has no nonzero nilpotents. Group the Laurent expansion of x in K by exponents modulo p, and
   take p-th roots of its coefficients in k. This gives x=sum_(j=0)^(p-1) t^j y_j^p with y_j in K.
   Frobenius commutes with these sums because the identity for finite truncations holds modulo
   every t^N and A is separated. The valuations of nonzero terms t^j y_j^p have distinct residues
   j modulo p, so a sum of such terms cannot vanish: the term of least valuation has nonzero
   leading coefficient. Thus 1,t,...,t^(p-1) is a basis of K over K^p and [K:K^p]=p. Iterating the
   field identity K=K^p(t) gives K=K^(p^n)(t) for every n: raise it to p^i to obtain
   K^(p^i)=K^(p^(i+1))(t^(p^i)), and substitute successively.

8. For any intermediate field K subset F subset E, F/K is finite. The Frobenius isomorphisms F ->
   F^p and K -> K^p transport any K-basis of F to a K^p-basis of F^p, so [F^p:K^p]=[F:K]. The
   tower K^p subset K subset F is finite by degree multiplicativity, and therefore F/F^p is finite
   by the finite-intermediate-field lemma. Comparing the two towers from K^p to F gives
   [F:F^p][F:K]=[F:K]p. Since [F:K] is a positive integer, [F:F^p]=p.

9. Let S be the separable algebraic closure of K in E. The separable-first lemma says S/K is
   separable and E/S is purely inseparable; both are finite by the finite-intermediate-field
   lemma. Apply lem-weil-pbc-purely-inseparable-pth-root-tower to obtain S=F_0 subset F_1 subset
   ... subset F_r=E, with F_i=F_(i-1)(alpha_i), alpha_i^p in F_(i-1), and [F_i:F_(i-1)]=p. Taking
   p-th powers of rational expressions in alpha_i shows F_i^p subset F_(i-1). Step 8 applied to
   F_i gives [F_i:F_i^p]=p, so degree multiplicativity forces F_i^p=F_(i-1). Iterating yields
   E^(p^r)=S. The case E=S gives the empty tower r=0 and the same equality.

10. Put q=p^r. By lem-sfb-separable-powers-generate, S=K(S^q). Step 7 gives K=K^q(t), hence
   S=S^q(t), since K^q subset S^q. By E^q=S there is u in E with u^q=t. For x in E, write x^q in
   S=S^q(t) as a rational expression in t whose finitely many coefficients are q-th powers of
   elements of S. Taking those coefficient roots and replacing t by u gives y in S(u) with
   y^q=x^q; the denominator stays nonzero because its q-th power is the original nonzero
   denominator. Frobenius is injective in E, so x=y. Therefore E=S(u)=S K[t^(1/p^r)], with the
   required finite separable E_s=S contained in E. This argument works for each specified t; for
   r=0 one can simply take u=t.

11. Construct a normal overfield next. If char K=0, take any finite normal overfield N/K
   containing E by lem-weil-pbc-finite-extension-in-finite-normal-extension. The characteristic-
   zero clause of lem-weil-pbc-separable-first-purely-inseparable, applied to N/E, says that every
   element of N is separable over E, as required. These two characteristics exhaust the cases: a
   positive characteristic of K must equal p because A injects into K and has a nonzero residue
   field of characteristic p.

12. In characteristic p use S,u,q from steps 9-10. The finite-Galois-receiving lemma for the
   single extension S/K gives a finite normal separable T/K and a K-embedding tau:S -> T. Work in
   an algebraically closed overfield Omega containing E. Extend the map tau(S) -> Omega, tau(s)
   |-> s, to an embedding T -> Omega by lem-weil-pbc-algebraic-extension-embeds-algebraically-
   closed. Here T/tau(S) is finite by the finite-intermediate-field lemma. Replace T by this
   image; it is now an actual subfield of Omega containing S, without changing its finite, normal
   or separable properties over K.

13. The field K(u) is the splitting field of X^q-t: in Omega this polynomial is (X-u)^q, and its
   only root is u. It is nonconstant, also when q=1. Apply lem-sfb-splitting-field-finite-normal
   to get K(u)/K finite normal. Put N=T K(u) inside Omega. By lem-sfb-finite-normal-field-
   compositum it is finite normal over K, and it contains E=S K(u). Moreover N=E(T), since S
   subset T and E=S K(u). Every element of T is separable over K; lem-sfb-separable-generated-
   scalar-extension with base field M=E and U=T gives N/E separable. This completes the normal-
   overfield assertion in characteristic p. The residue and ramification assertions for E were
   proved in steps 1-4; the same argument also applies to N/E over the complete DVR C with residue
   k.
-/
theorem complete_coefficient_field_arithmetic
    (A : Type u) (K : Type v) (E : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field E] [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    [FiniteDimensional K E] [IsAlgClosed (IsLocalRing.ResidueField A)]
    (p : ℕ) (hp : 0 < p) [CharP (IsLocalRing.ResidueField A) p] :
    (∃ (hC : IsLocalRing (integralClosure A E))
        (hf : IsLocalHom (algebraMap A (integralClosure A E))),
      Function.Bijective (IsLocalRing.ResidueField.map
        (algebraMap A (integralClosure A E))) ∧
      (IsLocalRing.maximalIdeal A).map (algebraMap A (integralClosure A E)) =
        IsLocalRing.maximalIdeal (integralClosure A E) ^ Module.finrank K E) ∧
    (∃ (N : Type (max v w)) (hN : Field N) (aKN : Algebra K N) (aEN : Algebra E N),
      IsScalarTower K E N ∧ FiniteDimensional K N ∧ Normal K N ∧ Algebra.IsSeparable E N) ∧
    (CharP K p → ∀ t : A, IsLocalRing.maximalIdeal A = Ideal.span {t} →
      ∃ (S : IntermediateField K E) (r : ℕ) (z : E),
        FiniteDimensional K S ∧ Algebra.IsSeparable K S ∧
        z ^ (p ^ r) = algebraMap A E t ∧
        S ⊔ IntermediateField.adjoin K ({z} : Set E) = ⊤) := by
  sorry

end IsDiscreteValuationRing
