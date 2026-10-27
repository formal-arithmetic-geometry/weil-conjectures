/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q130
-/
module

public import Sheaf.RingTheory.FormalMonoidExtensionModel
import Mathlib.RingTheory.FiniteType
import WeilConjectures.RingTheory.FiniteCompletionFactorIdempotent
import WeilConjectures.RingTheory.LocalCompletionQuotient
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Sheaf.TraceFormula.FsFaceSharpening
import Sheaf.RingTheory.FormalMonoidImplicitElimination

/-!
# Completed local models for invertible Kummer monoid extensions

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé VI 2.3,
printed p. 73; arbitrary unit faces and chart twists are the explicit algebraic
refinement recorded in the DAG
(blueprint: lem-per-completed-invertible-kummer-monoid-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Algebra

/-- An invertible Kummer extension preserves the equal-characteristic formal monoid
model and the mixed-characteristic parameter hypersurface model. The canonical chart
tensor ring, unit-face sharpenings and boundary ideal are those of
`def-per-formal-monoid-extension-data`; the conclusion retains the residue field,
the actual extended boundary ideal, and continuity in both directions.

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé VI 2.2--2.3,
printed pp. 72--73; arbitrary faces and unit twists are an agent-formulated refinement
(blueprint: lem-per-completed-invertible-kummer-monoid-extension).

Proof plan:
1. Choose generators $q_i$ of $Q$ and integers $d_i>0$ with $d_iq_i=h(r_i)$. The tensor ring $C$
   is generated over $A$ by their monomials, each satisfying $Z_i^{d_i}=\alpha(r_i)$; the
   finitely many products with exponents less than $d_i$ span $C$ as an $A$-module. Thus $C$ is
   finite type and Noetherian by the cited permanence result. Apply the finite-completion-factor
   statement with $R=A$, $S'=S=C$ and $g=1$: it identifies $\widehat B$ with the selected
   idempotent factor of $\widehat A\otimes_A C$. All monomials and their generated ideals are
   preserved. We can therefore perform the calculation over the displayed complete presentation
   of $\widehat A$.
2. The local map $A\to B$ reflects units, so $G,F$ are faces and $h^{-1}F=G$. Face sharpening
   gives sharp fs monoids $S,T$ with finite free group completions. For $f\in F$, choose $r\in
   R^{\rm gp}$ with $h(r)=Nf$, and use the Kummer condition to write $df=h(r_0)$ with $r_0\in
   R$, $d>0$. Injectivity gives $dr=Nr_0\in R$, so saturation gives $r\in R$. Since
   $[h(r)]=[f]^N$ is a unit in $B$, locality gives $r\in G$. Thus $NF^{\rm gp}\subset h(G^{\rm
   gp})$, and $h_U:G^{\rm gp}\hookrightarrow F^{\rm gp}$ has finite cokernel killed by $N$. The
   induced $\beta:S\to T$ sends only $0$ to $0$: if $h(r-g)$ is a unit in $Q_F$, then $h(r)$
   belongs to $F$ and $r\in G$.
3. Put $U=G^{\rm gp}$ and $V=F^{\rm gp}$. Split each quotient group sequence using lifts of a
   basis of the free groups $S^{\rm gp}$ and $T^{\rm gp}$. These group sections restrict to
   monoid sections: a lift of a monoid class differs from any representative by a unit, which
   can be added or subtracted in the localized monoid. Thus $R_G\cong U\oplus S$ and $Q_F\cong
   V\oplus T$. In these coordinates $h(u,s)=(h_U(u)+c(s),\beta(s))$, with $c:S^{\rm gp}\to V$.
   Write $\alpha(u,s)=\rho(u)e(s)a(s)$; here $\rho=\alpha|_U$ and $e(s)=\epsilon(j_S(s))$ are
   unit characters, because $\alpha=\epsilon a$ and the section $j_S$ is additive. No extension
   of $\epsilon$ to $Q^{\rm gp}$ is needed, and neither $U$ nor $V$ is assumed torsion free.
4. With $A_0=\widehat A$, impose the unit relations first: $A_1=A_0\otimes_{\mathbf Z[U]}\mathbf
   Z[V]$, using $\rho:U\to A_0^\times$. The tame group-algebra lemma applies to the injective
   map $h_U$ with finite cokernel killed by the invertible $N$, even if its unit groups have
   torsion. It gives complete local finite etale factors $K$. The split monoid presentation
   gives the remaining relations $[c(s)]Y^{\beta(s)}=e(s)X^s$. After completing at the chosen
   prime, exactly one factor $K$ occurs: modulo the nonzero $T$-monomials all nonzero
   $S$-monomials vanish by these relations, so the residue prime is precisely a closed-point
   factor of $A_1$. In particular its residue field equals $\kappa(\mathfrak q)$.
5. Put $E=k[[t_1,\ldots,t_n]]$ in case (a), and $E=V[[t_1,\ldots,t_n]]$ in case (b). The power-
   series/Cohen statement makes $E$ nonzero complete regular Noetherian local. Iterating the
   defining inverse limits of the formal monoid presentations gives $A_0=E[[S]]/(f)$, where
   $f=0$ in case (a) and $f=\theta$ in case (b). Apply the finite-etale formal-monoid
   coefficient-lift lemma to the selected local finite etale $A_0$-algebra $K$. It supplies a
   nonzero complete regular Noetherian local finite etale $E$-algebra $D$ with residue field
   $\kappa(\mathfrak q)$ and $K\cong D[[S]]/(f)$. In mixed characteristic it also preserves
   every nonzero cotangent class from $E$.
6. Under this isomorphism the unit character $e(s)[c(s)]^{-1}$ in $K$ lifts to a character
   $v:S^{\rm gp}\to D[[S]]^\times$: choose arbitrary unit lifts of its values on a basis of the
   free group $S^{\rm gp}$ and extend multiplicatively; reduction recovers the given character.
   This needs no root extraction. The completed presentation of the selected factor is therefore
   $$D[[S\oplus T]]/(f,\ Y^{\beta(s)}-v(s)X^s\ (s\in S)).$$ To check this presentation, start
   with $R_G=U\oplus S$ and $Q_F=V\oplus T$, take the balanced tensor quotient on their monomial
   generators, impose the unit relations to obtain $K$, and then complete. Completion of the
   quotient is the quotient of the completion by the generated relations by the cited theorem.
   All these rings are Noetherian: the monoids are finitely generated and finite-type permanence
   and completion preserve Noetherianity. Changing unit lifts changes the displayed relations
   only by multiples of $f$.
7. Apply implicit monoid elimination with coefficient ring $D$, monoids $S,T$, the map $\beta$
   (whose inverse image of $0$ is $\{0\}$), and character $u(s)=v(s)^{-1}$. The relations are
   $X^s-u(s)Y^{\beta(s)}$. The lemma identifies their quotient with $D[[T]]$, sends each nonzero
   $S$-monomial into the nonzero-$T$ ideal, and is the identity on $D$ on the stratum. Thus in
   equal characteristic the required ring is $D[[T]]$. In mixed characteristic the additional
   relation becomes the image $\eta$ of $\theta$, so the required ring is $D[[T]]/(\eta)$.
8. In mixed characteristic reduce the elimination substitution modulo the nonzero $T$-monomials.
   Every nonzero $S$-monomial is zero and the coefficients are fixed, so $\overline\eta$ is the
   image of $\theta_0=\theta|_{S=0}\in E$. The hypothesis says $\theta_0\equiv p$ modulo
   $(t_1,\ldots,t_n)$. In the regular power-series ring $E=V[[t]]$, its linear term in the
   parameter $p$ has coefficient $1$, so $\theta_0\in\mathfrak m_E\setminus\mathfrak m_E^2$,
   including $n=0$. The coefficient-lift lemma preserves this class in $D$, proving
   $\overline\eta\in\mathfrak m_D\setminus\mathfrak m_D^2$.
9. Finally $Q_F=V\oplus T$ identifies a monomial from $Q\setminus F$ with a unit times $Y^t$ for
   $t\ne0$. Conversely any $t\ne0$ has a representative $q-f$ with $q\notin F$, so $Y^t$ is a
   unit times the image of $[q]$. Hence the two generated ideals coincide, before and after
   completion and after the mixed quotient. The elimination isomorphism fixes $Y$-monomials, so
   it identifies $J\widehat B$ with the indicated nonzero-$T$ ideal. Each isomorphism was formed
   on completed local rings and respects their ideals of definition, hence is continuous. The
   ring $D$ and its residue field are those of Step 5. This proves the asserted pairs in both
   cases, also for $T=\{0\}$.
-/
theorem completedInvertibleKummerMonoidExtension_model
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (R : Type v) [CommMonoid R] (Q : Type w) [CommMonoid Q]
    (_hR : AlgebraicGeometry.IsFineSaturatedMonoid R)
    (_hQ : AlgebraicGeometry.IsFineSaturatedMonoid Q) (h : R →* Q)
    (_hinj : Function.Injective h)
    (_hkummer : ∀ q : Q, ∃ (d : ℕ) (_ : 0 < d) (r : R), h r = q ^ d)
    (_hgp : Function.Injective
      (GrothendieckGroup.lift ((GrothendieckGroup.of (M := Q)).comp h)))
    [Finite (GrothendieckGroup Q ⧸
      (GrothendieckGroup.lift ((GrothendieckGroup.of (M := Q)).comp h)).range)]
    (N : ℕ) (_hN : 0 < N)
    (_hkill : ∀ q : GrothendieckGroup Q, q ^ N ∈
      (GrothendieckGroup.lift ((GrothendieckGroup.of (M := Q)).comp h)).range)
    (_hunit : IsUnit (N : A))
    (α : R →* A) (a : Multiplicative (chartSharpMonoid α) →* A)
    (ε : GrothendieckGroup R →* Aˣ)
    (_hα : ∀ r : Localization ((IsUnit.submonoid A).comap α),
      localizedUnitChart α r =
        (ε (unitChartGroupMap α r) : A) * a (Multiplicative.ofAdd
          (Additive.ofMul (Associates.mk r))))
    (q : Ideal (monoidChartTensor α h)) [q.IsPrime]
    (_hq : Ideal.comap (monoidChartTensorBase α h) q = IsLocalRing.maximalIdeal A) :
    ((∃ (n : ℕ)
        (e : AddMonoidAlgebra.CompletedLocalModel (IsLocalRing.ResidueField A)
          (chartSharpMonoid α) n ≃+* AdicCompletion (IsLocalRing.maximalIdeal A) A),
        ∀ s : chartSharpMonoid α,
          e (algebraMap (MvPolynomial (Fin n)
              (AddMonoidAlgebra (IsLocalRing.ResidueField A) (chartSharpMonoid α))) _
            (MvPolynomial.C (AddMonoidAlgebra.single s (1 : IsLocalRing.ResidueField A)))) =
            algebraMap A _ (a (Multiplicative.ofAdd s))) →
      AddMonoidAlgebra.HasExtendedFormalMonoidModel (Localization.AtPrime q)
        (chartSharpMonoid (localizedTensorMonomial α h q))
        (localizedTensorBoundary α h q) false) ∧
    ((∃ (V : Type (max u v w)) (_ : CommRing V) (_ : IsLocalRing V) (p : ℕ),
        IsCohenRing p V ∧
        Nonempty (IsLocalRing.ResidueField V ≃+* IsLocalRing.ResidueField A) ∧
        ∃ (n : ℕ) (θ : AddMonoidAlgebra.CompletedLocalModel V (chartSharpMonoid α) n),
          θ - (p : AddMonoidAlgebra.CompletedLocalModel V (chartSharpMonoid α) n) ∈
            AddMonoidAlgebra.completedLocalModelBoundaryIdeal V (chartSharpMonoid α) n ∧
          ∃ e : (AddMonoidAlgebra.CompletedLocalModel V (chartSharpMonoid α) n ⧸
              Ideal.span {θ}) ≃+* AdicCompletion (IsLocalRing.maximalIdeal A) A,
            ∀ s : chartSharpMonoid α,
              e (Ideal.Quotient.mk (Ideal.span {θ})
                (algebraMap (MvPolynomial (Fin n)
                    (AddMonoidAlgebra V (chartSharpMonoid α))) _
                  (MvPolynomial.C (AddMonoidAlgebra.single s (1 : V))))) =
                  algebraMap A _ (a (Multiplicative.ofAdd s))) →
      AddMonoidAlgebra.HasExtendedFormalMonoidModel (Localization.AtPrime q)
        (chartSharpMonoid (localizedTensorMonomial α h q))
        (localizedTensorBoundary α h q) true) := by
  sorry

end Algebra
