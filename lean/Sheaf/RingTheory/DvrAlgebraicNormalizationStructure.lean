module

public import Sheaf.RingTheory.EppEssentiallyFiniteTypeTraits
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.Spectrum.Maximal.Defs

import Mathlib.RingTheory.Localization.Integral
import WeilConjectures.AlgebraicGeometry.IntegralClosureDedekindSurjectiveFibres
import WeilConjectures.Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.RingTheory.ReducedNoetherianTotalRingFractions
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import WeilConjectures.RingTheory.SemilocalNormalizationDimOne
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.DedekindDomain.Dvr
import WeilConjectures.RingTheory.DimOneResidueFieldsFinite

/-!
# Structure of algebraic normalized DVR base changes

Source: Stacks Project, More on Algebra, Tags 09EM and 09IH
(blueprint: lem-sfb-dvr-algebraic-normalization-structure).

The reduced tensor algebra and the canonical map between normalizations are the
constructions already used by the Epp theorem. Finite generation of residue fields
is field generation, so transcendental residue extensions are allowed.
-/

@[expose] public section

set_option autoImplicit false

universe u v w x y

namespace IsDiscreteValuationRing

/-- Structure of the lower and upper normalizations for an algebraic extension.

Source: Stacks Project, More on Algebra, Tag 09EM (`remark-construction`),
Tag 09IH (`lemma-big-extension-is-ok`), and Algebra, Tag 031F
(blueprint: lem-sfb-dvr-algebraic-normalization-structure).

Proof:
1. Write $R=R_P$, $C=C_P$, $E=E_P$ and choose a uniformizer $\pi$ of $A$. The algebraic
   integral-closure theorem gives $A\subset R\subset P$, $\operatorname{Frac}(R)=P$, and
   normality of $R$. In case (a), the finite-extension Dedekind theorem makes $R$ Noetherian of
   dimension one; in case (b), Noetherianity is assumed and integral dimension invariance gives
   dimension one. All maximal ideals of $R$ contract to $\mathfrak m_A$, so all contain $\pi$.
   Every prime containing $\pi$ is maximal by integrality over $A$. They are consequently all
   minimal over $(\pi)$, and are finite in number by the finite-minimal-primes theorem. Thus $R$
   is a semilocal normal Noetherian domain of dimension one in both cases. Uses: lem-weil-pbc-
   integral-closure-algebraic-extension-normal, lem-sc-integral-closure-dedekind-surjective-
   fibres, lem-weil-pbc-integral-injective-dimension-equal, lem-weil-pbc-integral-maximal-
   contracts-maximal, lem-weil-pbc-integral-prime-over-maximal-maximal, lem-sc-finite-minimal-
   primes-over-ideal.
2. The $A$-modules $B$ and $R$ are torsion free, hence flat over the PID $A$. Since $A\to B$ is
   local it is faithfully flat. Put $D=B\otimes_A R$. Base change makes $R\to D$ faithfully
   flat, and makes $B\to D$ integral. Flatness of $R$ preserves the injection $A\hookrightarrow
   B$, so $R\hookrightarrow D$; flatness of $B$ similarly gives $B\hookrightarrow D$. Tensoring
   multiplication by $\pi$ on $R$ with the flat module $B$ shows that $\pi$ is a nonzerodivisor
   of $D$. The image of $\pi$ in $B$ is a positive power of a uniformizer times a unit, since
   the map of DVRs is injective and local. Uses: lem-weil-pbc-pid-torsion-free-module-flat, lem-
   weil-pbc-flat-local-hom-faithfully-flat, lem-weil-pbc-faithfully-flat-base-change, lem-weil-
   pbc-integral-base-change, def-weil-pbc-flat-ring-map, def-sc-discrete-valuation-ring.
3. We have $R[1/\pi]=P$: for $x\in P$, multiply a polynomial equation over $K$ by a sufficiently
   large power of $\pi$ after replacing $x$ by $\pi^N x$, to obtain a monic equation for $\pi^N
   x$ over $A$. Hence $\pi^N x\in R$. The localization-tensor theorem now identifies $D[1/\pi]$
   with $L\otimes_K P$, because $B[1/\pi]=L$. On pure fractions the identification is $(b\otimes
   r)/\pi^j\mapsto (b/\pi^j)\otimes r$, and its inverse is obtained by putting the finitely many
   denominators into one power of $\pi$. Reduction commutes with this localization: $d/\pi^j$ is
   nilpotent exactly when $\pi^k d^h=0$ for some $k,h$, which, by regularity of $\pi$, means $d$
   is nilpotent. Thus, for $G=D_{\mathrm{red}}$, $E=G[1/\pi]$ and $G\hookrightarrow E$. Uses:
   lem-weil-pbc-localization-tensor-product.
4. The algebra $L\otimes_KP$ is nonzero, since field-extension base change is faithfully flat
   and therefore injective. Its reduction is nonzero too (otherwise $1$ would be nilpotent).
   Since an algebraic field extension is integral, integral base change makes $L\to
   L\otimes_KP$, and hence $L\to E$, integral. Every prime of $E$ is maximal, being over the
   unique prime of the field $L$. In particular, all its residue fields are algebraic over $L$:
   a monic equation for an element descends to the quotient field $E/\mathfrak q$. Uses: lem-
   weil-pbc-field-extension-base-change-faithfully-flat, lem-weil-pbc-faithfully-flat-
   universally-injective, lem-weil-pbc-integral-base-change, lem-weil-pbc-integral-prime-over-
   maximal-maximal.
5. In case (a), choosing a finite $K$-basis of $P$ shows that $L\otimes_KP$, and therefore $E$,
   is finite-dimensional over $L$. Thus $E$ is Artinian, and its reduced Artinian decomposition
   gives $E=\prod_{i=1}^t F_i$ with $t\ge1$ and each $F_i/L$ finite. The integral closure $C_i$
   of $B$ in $F_i$ is a Dedekind domain by the finite-extension Dedekind theorem. That theorem
   gives finite fibres of $\operatorname{Spec}(C_i)\to\operatorname{Spec}(B)$; maximal ideals
   contract to the unique maximal ideal of $B$, so $C_i$ is semilocal. Integrality is
   coordinatewise for a finite product: one implication projects a monic equation; for the
   converse the product of the finitely many monic equations annihilates the tuple. Hence
   $C=\prod_i C_i$, a Noetherian semilocal product of normal domains of dimension one. Uses:
   lem-weil-pbc-finite-dim-algebra-artinian, lem-sfb-reduced-artinian-residue-product, lem-sc-
   integral-closure-dedekind-surjective-fibres, lem-weil-pbc-integral-maximal-contracts-maximal.
6. For case (b), choose $B=U_{\mathfrak p}$ with $U$ a finite type $A$-algebra. Then $D$ is the
   localization of the finite type $R$-algebra $U\otimes_A R$ at the image of
   $U\setminus\mathfrak p$. The finite-type and localization permanence theorems show $D$ is
   Noetherian. Integral dimension invariance for $B\hookrightarrow D$ gives $\dim D=1$. Every
   maximal ideal of $D$ contracts to $\mathfrak m_B$ and contains $\pi$; conversely every prime
   containing $\pi$ contracts to $\mathfrak m_B$ and is maximal. Thus these primes are precisely
   the minimal primes over $(\pi)$ and there are finitely many. So $D$ is semilocal. Quotients
   $G$ and $D/\mathfrak a$ are Noetherian too: they are finite type $D$-algebras. Uses: lem-
   weil-pbc-finite-type-algebra-noetherian, lem-weil-pbc-localization-noetherian, lem-weil-pbc-
   integral-injective-dimension-equal, lem-weil-pbc-integral-maximal-contracts-maximal, lem-
   weil-pbc-integral-prime-over-maximal-maximal, lem-sc-finite-minimal-primes-over-ideal.
7. Still in case (b), $E=G[1/\pi]$ is Noetherian by localization. It is reduced and every prime
   is maximal by step 4, hence also minimal. Apply the reduced Noetherian total-fraction-ring
   decomposition to $E$. Every nonzerodivisor is a unit: otherwise it belongs to some maximal
   ideal, which is minimal, whereas the cited decomposition says nonzerodivisors avoid all
   minimal primes. Thus $Q(E)=E$, so the cited isomorphism gives a nonempty finite product
   $E=\prod_i F_i$ of fields, all algebraic over $L$ by step 4. Under localization, these
   factors correspond to the minimal primes $\mathfrak a_i$ of $D$. Indeed all minimal primes
   avoid the nonzerodivisor $\pi$; primes surviving inversion of $\pi$ contract to zero in $B$,
   and integral incomparability says any two comparable such primes are equal. Localizing
   $D/\mathfrak a_i$ at $\pi$ is therefore exactly the factor field $F_i$, which is its fraction
   field. Uses: lem-weil-pbc-localization-noetherian, lem-weil-pbc-reduced-noetherian-total-
   ring-fractions, lem-pc-minimal-prime-avoids-nonzerodivisor, lem-weil-pbc-integral-
   incomparability.
8. For each $i$ in case (b), put $T_i=D/\mathfrak a_i\subset F_i$. The contraction of $\mathfrak
   a_i$ to $B$ is zero: it avoids $\pi$, and every nonzero prime of the DVR $B$ contains $\pi$.
   Thus $B\hookrightarrow T_i$ is integral. Integral dimension invariance gives $\dim T_i=1$. It
   is Noetherian by step 6 and semilocal because its maximal ideals are maximal ideals of $D$
   containing $\mathfrak a_i$. Apply semilocal dimension-one normalization to $T_i$ in its own
   fraction field $F_i$. Its normalization $C_i$ is a semilocal Dedekind domain. It is also the
   integral closure of $B$ in $F_i$: an element integral over $B$ is integral over $T_i$, and
   the converse follows from transitivity of integral maps. The coordinatewise monic-polynomial
   argument of step 5 gives $C=\prod_i C_i$. Finite products of Noetherian rings are Noetherian,
   since their ideals are products of the component ideals; maximal ideals of a finite product
   come from one factor. Consequently $C$ is Noetherian and semilocal with normal domain factors
   of dimension one. Uses: lem-weil-pbc-integral-injective-dimension-equal, lem-sc-semilocal-
   dim-one-normalization, lem-weil-pbc-integral-transitive.
9. The image of $R$ in $E$ lies in $C$, because its elements are integral over $A$, hence over
   $B$. This gives the required $R\to C$ and the map $D\to C$. The latter is integral, since
   every element of $C$ already satisfies a monic equation over $B$. Its kernel is the
   nilradical: the map $D\to E$ has precisely that kernel by step 3, and $C\subset E$. Therefore
   $G\hookrightarrow C$ is integral and injective. Lying over makes
   $\operatorname{Spec}C\to\operatorname{Spec}G=\operatorname{Spec}D$ surjective. Faithful
   flatness of $R\to D$ makes $\operatorname{Spec}D\to\operatorname{Spec}R$ surjective as well.
   For any maximal $n$ of $R$, select a prime $\mathfrak d$ of $D$ over $n$, then a prime $q$ of
   $C$ over $\mathfrak d$. Since $\pi\in n$, $\mathfrak d$ contains $\pi$ and is maximal
   (integrality over $B$); integrality of $D\to C$ then makes $q$ maximal. Thus every maximal
   ideal of $R$ is attained. Uses: lem-weil-pbc-integral-injective-lying-over, lem-weil-pbc-
   faithfully-flat-surjective-spectrum, lem-weil-pbc-integral-prime-over-maximal-maximal.
10. Conversely, for a maximal ideal $q$ of $C$, integrality over $B$ shows $q\cap B=\mathfrak
   m_B$. Hence $\pi\in q$ and $n=q\cap R$ is a prime containing $\pi$, therefore maximal by
   integrality of $R/A$. Step 1 makes $R$ a Dedekind domain, and steps 5 or 8 make the factor of
   $C$ selected by $q$ a Dedekind domain. The Dedekind-localization theorem gives the DVRs $R_n$
   and $C_q$; localizing a product at a prime of one factor kills all the other factors. The
   homomorphism $R_n\to C_q$ is defined by $r/s\mapsto r/s$, since $s\notin n$ implies its image
   is outside $q$. Its maximal ideal contracts to $nR_n$, so it is local. Uses: lem-weil-pbc-
   integral-maximal-contracts-maximal, lem-weil-pbc-integral-prime-over-maximal-maximal, lem-sc-
   dedekind-localization-dvr.
11. In case (a), apply the finite-extension Dedekind theorem to $A\subset R$ and to each
   $B\subset C_i$ of step 5. It states that all residue field extensions are finite. Since $n$
   and $q$ contract to the maximal ideals of $A$ and $B$, respectively, these are exactly the
   two finite extensions asserted in (a). This application uses no separability hypothesis.
   Uses: lem-sc-integral-closure-dedekind-surjective-fibres.
12. In case (b), let $q_i$ be the maximal ideal in the factor $C_i$ selected by $q$ and let
   $\mathfrak d_i=q_i\cap T_i$. It is maximal by integrality; $T_{i,\mathfrak d_i}$ is a
   Noetherian local domain of dimension one, since $T_i$ is a one-dimensional domain and
   $\mathfrak d_i\ne0$ (it contains $\pi$). The inclusion $T_{i,\mathfrak d_i}\hookrightarrow
   (C_i)_{q_i}$ has the same fraction field $F_i$ on both sides. The dimension-one finite-
   residue theorem, applied with extension degree one, gives $\kappa(q_i)/\kappa(\mathfrak d_i)$
   finite. The prime $\mathfrak d_i$ lifts to a prime of $U\otimes_A R$; quotienting by
   $\mathfrak a_i$ and localizing do not change its residue field, so the finite-type residue
   theorem for $R\to U\otimes_A R$ gives $\kappa(\mathfrak d_i)/\kappa(n)$ finitely generated.
   Adjoin these finitely many field generators and then a finite basis of $\kappa(q_i)$ over the
   intermediate field: their union generates $\kappa(q)=\kappa(q_i)$ over $\kappa(n)$. This
   proves the residue assertion of (b). Uses: lem-weil-pbc-integral-maximal-contracts-maximal,
   lem-weil-pbc-localization-noetherian, lem-weil-pbc-dim-one-residue-field-extensions-finite,
   lem-weil-pbc-finite-type-residue-field-extension-finitely-generated.
-/
theorem algebraic_normalization_structure
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    (B : Type v) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (hinj : Function.Injective (algebraMap A B))
    (K : Type w) [Field K] [Algebra A K] [IsFractionRing A K]
    (L : Type x) [Field L] [Algebra B L] [IsFractionRing B L]
    [Algebra A L] [Algebra K L] [IsScalarTower A B L] [IsScalarTower A K L]
    (P : Type y) [Field P] [Algebra K P] [Algebra.IsAlgebraic K P]
    [Algebra A P] [IsScalarTower A K P]
    (hcase : Module.Finite K P ∨
      ((∃ (U : Type (max u v)) (_ : CommRing U) (_ : Algebra A U)
        (p : Ideal U) (_ : p.IsPrime),
        RingHom.FiniteType (algebraMap A U) ∧
          Nonempty (B ≃ₐ[A] Localization.AtPrime p)) ∧
        IsNoetherianRing (integralClosure A P))) :
    (∃ (t : ℕ) (_ : 0 < t) (F : Fin t → Type (max x y))
      (_ : ∀ i, Field (F i)) (_ : ∀ i, Algebra L (F i)),
      (∀ i, Algebra.IsAlgebraic L (F i)) ∧
        Nonempty (eppReducedTensor K L P ≃ₐ[L] ∀ i, F i)) ∧
    IsNoetherianRing (integralClosure A P) ∧
    IsNoetherianRing (eppUpperClosure B K L P) ∧
    Finite (MaximalSpectrum (integralClosure A P)) ∧
    Finite (MaximalSpectrum (eppUpperClosure B K L P)) ∧
    IsDomain (integralClosure A P) ∧
    (∃ (t : ℕ) (D : Fin t → Type (max x y)) (_ : ∀ i, CommRing (D i))
      (_ : ∀ i, IsDomain (D i)),
      (∀ i, IsIntegrallyClosed (D i)) ∧
      (∀ i, (∀ (p : Ideal (D i)), p.IsPrime → p ≠ ⊥ → p.IsMaximal) ∧
        ∃ (p : Ideal (D i)), p.IsPrime ∧ p ≠ ⊥) ∧
      Nonempty (eppUpperClosure B K L P ≃+* ∀ i, D i)) ∧
    (∀ (q : Ideal (eppUpperClosure B K L P)) [q.IsMaximal],
      (q.comap (eppNormalizationMap A B K L P)).IsMaximal ∧
      IsDiscreteValuationRing
        (Localization.AtPrime (q.comap (eppNormalizationMap A B K L P))) ∧
      (∃ hdom : IsDomain (Localization.AtPrime q),
        @IsDiscreteValuationRing (Localization.AtPrime q) _ hdom) ∧
      (((∃ (U : Type (max u v)) (_ : CommRing U) (_ : Algebra A U)
          (p : Ideal U) (_ : p.IsPrime),
          RingHom.FiniteType (algebraMap A U) ∧
            Nonempty (B ≃ₐ[A] Localization.AtPrime p)) ∧
          IsNoetherianRing (integralClosure A P)) →
        @IntermediateField.FG
          (q.comap (eppNormalizationMap A B K L P)).ResidueField _ q.ResidueField _
          (Ideal.ResidueField.map (q.comap (eppNormalizationMap A B K L P)) q
            (eppNormalizationMap A B K L P) rfl).toAlgebra ⊤)) ∧
    (∀ (n : Ideal (integralClosure A P)) [n.IsMaximal],
      ∃ (q : Ideal (eppUpperClosure B K L P)) (_ : q.IsMaximal),
        q.comap (eppNormalizationMap A B K L P) = n) ∧
    (Module.Finite K P →
      (∀ (n : Ideal (integralClosure A P)) [n.IsMaximal],
        RingHom.Finite (algebraMap A n.ResidueField)) ∧
      (∀ (q : Ideal (eppUpperClosure B K L P)) [q.IsMaximal],
        RingHom.Finite (algebraMap B q.ResidueField))) := by
  sorry

end IsDiscreteValuationRing
