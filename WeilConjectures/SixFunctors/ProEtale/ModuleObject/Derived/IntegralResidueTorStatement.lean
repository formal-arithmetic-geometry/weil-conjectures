/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.AlgebraicGeometry.IntegralReductionTower
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom

import WeilConjectures.AlgebraicGeometry.IntegralCriterionReductionsStatement

/-!
# Residue reduction controls integral Tor amplitude

Source:
literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
lem-coef-integral-residue-tor.md
Place: Complete statement, with the standing field/scheme/coefficient conventions made explicit; no
change to its objects, hypotheses or conclusions.
(blueprint: lem-coef-integral-residue-tor).

The statement uses the intrinsic condensed coefficient ring and the canonical derived
extension of scalars to each finite quotient.  The proof is postponed: the residue
cohomology interval is transported through the quotient tensor, the finite uniformizer
filtration gives the same interval at every level, and the integral criterion identifies
bounded constructibility with finite Tor amplitude.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Scheme
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Bounds on the first residue reduction give a common Tor interval at every finite
coefficient level, and identify the intrinsic bounded constructible and finite-Tor
subcategories for the integral condensed coefficient ring.

Source:
literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-smooth-purity/
sec-sp-grp-ladic-summary/sec-towers-and-integral-coefficients/sk-lem-sp-tower/
lem-coef-integral-residue-tor.md
Place: Complete statement, with the standing field/scheme/coefficient conventions made explicit; no
change to its objects, hypotheses or conclusions.
(blueprint: lem-coef-integral-residue-tor).

Proof (the landed six-step split):

1. The blueprint opens with the canonical balanced coefficient-tensor associativity identity:
$K_n\otimes^L_{(A_{E,n})_X}\kappa_X\simeq K\otimes^L_{R_X}\kappa_X=K_1$, where $A_{E,n}=R/(\pi_E^n)$
and $\kappa=A_{E,1}$. The coefficient maps compose to the first quotient; on tensor representatives
the balancing map is $(x\otimes u)\otimes v\mapsto x\otimes uv$, with inverse $x\otimes
v\mapsto(x\otimes1)\otimes v$. This records the opening associativity calculation, without the
former scalar-mate construction.

2. For the constructibility sentence, the integral criterion [sk-prop-integral-criterion],
(1)$\Rightarrow$(2), supplies derived completeness and bounded constructibility of $K_1$ from $K\in
D^b_c(X,R)$. For Noetherian $X$, [det-prop-integral-criterion-reductions] therefore supplies bounded
constructibility of every $K_n$. This is the reduction-constructibility step of the blueprint, not
an identification of a cohomological interval with a Tor interval. Its Noetherian hypothesis is the
standing separated finite-type-over-a-field setting.

3. Fix $n\ge1$ and write $A=A_{E,n}$. Since $A$ is finite discrete,
[lem-sf-module-object-ordinary-coefficient-equivalence] identifies its pulled-back condensed
coefficient ring with the constant ring sheaf on $X_{\mathrm{pro\acute et}}$, and preserves relative
derived tensors and Tor intervals. Use this ordinary module-sheaf presentation, on the same site.
Choose a complex representing $K_n$ and a K-flat resolution $P$ with flat terms by
[lem-pc-kflat-resolution]. By [def-weil-derived-tensor], $K_n\otimes_A^L M$ is represented by the
termwise tensor $P\otimes_A M$ for every module sheaf $M$ in degree zero. Step 1 and the hypothesis
on $K_1$ therefore give $H^i(P\otimes_A\kappa_X)=0$ whenever $i<a$ or $b<i$.

4. Let $r$ be the image of $\pi_E$ in $A$. The DVR and uniformizer assertions of
[lem-weil-l-adic-extension-integers-dvr] give $r^n=0$ and $A/(r)=\kappa$ a field; thus $(r)$ is
maximal, including when $n=1$ and $r=0$. For any $A_X$-module sheaf $N$ killed by $r$, apply
[lem-sf-proetale-residue-module-tensor-homology] to $T=X$, this ring $A$, the complex $P$, the
residue unit $\kappa_X$, and $N$. Its conclusion is $H^i(P\otimes_A N)=0$ for each $i$ outside
$[a,b]$, by the residue vanishing from step 3. This lemma is stated on the small pro-etale site for
arbitrary schemes and complexes; neither a finite-field datum nor constructibility is a hypothesis.

5. For any $A_X$-module sheaf $M$, put $M_j=\operatorname{im}(r^j:M\to M)$ for $0\le j\le n$. Then
$M_0=M$, $M_n=0$, and $G_j=M_j/M_{j+1}$ is killed by $r$, since $rM_j\subseteq M_{j+1}$. Each
sequence $0\to M_{j+1}\to M_j\to G_j\to0$ is short exact. Flatness of $P^q$ means its tensor functor
is exact [def-pc-flat-sheaf-modules]; applying the short-exact image assertion of
[lem-weil-pbc-exact-functor-ses-triangle-image] to this functor in every degree $q$ gives a
degreewise short exact sequence $0\to P\otimes_A M_{j+1}\to P\otimes_A M_j\to P\otimes_A G_j\to0$.
For each $i$ outside $[a,b]$, [lem-weil-pbc-complex-ses-homology-long-exact] gives the exact segment
$H^i(P\otimes M_{j+1})\to H^i(P\otimes M_j)\to H^i(P\otimes G_j)$. The last term is zero by step 4.
Descending induction from $M_n=0$ therefore makes the middle term zero, without enlarging the
interval. By step 3 this is the vanishing of $H^i(K_n\otimes_A^L M)$ for every $M$, hence precisely
Tor amplitude $[a,b]$ [def-weil-finite-tor-amplitude]. The same $[a,b]$ works for every $n$.

6. For the final equality over $R_X$ itself, apply [sk-prop-integral-criterion],
(1)$\Leftrightarrow$(4), to the Noetherian scheme $X$. Its two conditions say exactly $K\in
D^b_c(X,\mathcal O_E)$ and $K\in D^b_{ctf}(X,\mathcal O_E)$; thus it supplies the forward inclusion
for every $K$, not merely a condition on reductions. The reverse inclusion is also part of
[sk-def-sfb-constructible], which defines the finite-Tor category as a full subcategory of $D^b_c$.
Since both are full subcategories of the same ordinary derived category, equality of these object
conditions gives the stated equality of full subcategories. No identification with site-perfectness
is made.
-/
theorem integralResidueTor
    (p ℓ : ℕ) [Fact p.Prime] [Fact ℓ.Prime] (_hpℓ : ℓ ≠ p)
    (k : Type u) [Field k] [CharP k p] (_hk : Finite k ∨ IsAlgClosed k)
    (X : Over (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (π : {π : PadicAlgCl.integers ℓ E.1 //
      Ideal.span ({π} : Set (PadicAlgCl.integers ℓ E.1)) =
        IsLocalRing.maximalIdeal (PadicAlgCl.integers ℓ E.1)}) :
    letI : MonObj (Profinite.padicIntegersRingObj.{u} ℓ E.1) :=
      Sheaf.monObj_sheafCompose_obj (coherentTopology Profinite.{u})
        (Profinite.padicIntegersCondensedRing ℓ E.1)
    letI : IsCommMonObj (Profinite.padicIntegersRingObj.{u} ℓ E.1) :=
      Profinite.isCommMonObj_padicIntegersRingObj ℓ E.1
    letI (n : ℕ) : MonObj (integralQuotientRingObj ℓ E.1 π.1 n) :=
      Sheaf.monObj_sheafCompose_obj (coherentTopology Profinite.{u})
        (Profinite.continuousMapRingSheaf (integralQuotient ℓ E.1 π.1 n))
    letI (n : ℕ) : IsCommMonObj (integralQuotientRingObj ℓ E.1 π.1 n) :=
      Profinite.isCommMonObj_continuousMapRingObj (integralQuotient ℓ E.1 π.1 n)
    letI : MonObj (condensedRingObj
        (Profinite.padicIntegersRingObj.{u} ℓ E.1) X.left) :=
      ((upperStarFromPoint X.left).mapMon.obj
        (Mon.mk (Profinite.padicIntegersRingObj.{u} ℓ E.1))).mon
    letI : IsCommMonObj (condensedRingObj
        (Profinite.padicIntegersRingObj.{u} ℓ E.1) X.left) :=
      Functor.isCommMonObj_obj (F := upperStarFromPoint X.left)
    letI (n : ℕ) : MonObj (condensedRingObj
        (integralQuotientRingObj ℓ E.1 π.1 n) X.left) :=
      ((upperStarFromPoint X.left).mapMon.obj
        (Mon.mk (integralQuotientRingObj ℓ E.1 π.1 n))).mon
    letI (n : ℕ) : IsCommMonObj (condensedRingObj
        (integralQuotientRingObj ℓ E.1 π.1 n) X.left) :=
      Functor.isCommMonObj_obj (F := upperStarFromPoint X.left)
    (∀ (K : DerivedCategory
        (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
          (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left))),
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left) K →
      ∀ a b : ℤ, a ≤ b →
        _root_.DerivedCategory.homologyConcentratedIn a b
          ((CategoryTheory.Mod.extendScalars
            (integralReductionCoefficientMap X.left ℓ E.1 π.1 1)).leftDerivedFunctor.obj K) →
        ∀ n : ℕ, 1 ≤ n →
          _root_.DerivedCategory.torAmplitudeIn
            (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
              (condensedRingObj (integralQuotientRingObj ℓ E.1 π.1 n) X.left)) a b
            ((CategoryTheory.Mod.extendScalars
              (integralReductionCoefficientMap X.left ℓ E.1 π.1 n)).leftDerivedFunctor.obj K)) ∧
      boundedConstructible (condensedRingObj (Profinite.padicIntegersRingObj ℓ E.1) X.left) =
        condensedConstructibleFiniteTor (Profinite.padicIntegersRingObj ℓ E.1) X.left := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
