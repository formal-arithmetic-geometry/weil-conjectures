/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q35
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence

import Sheaf.SixFunctors.ProperBaseChangeModules
import Sheaf.Paper.EtaleDerivedDirectImageCoherence
import Sheaf.AlgebraicGeometry.ModuleExchangeCompositeBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.AlgebraicGeometry.QuasiExcellentFiniteTypeStability
import Sheaf.AlgebraicGeometry.QuasiFiniteFlatWeightedTrace
import Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
import Sheaf.AlgebraicGeometry.ConstructibleEtaleSetPullback
import WeilConjectures.RingTheory.QuasiFiniteLocalDimension
import Sheaf.AlgebraicGeometry.FiniteFinitePresentationPushforwardConstructible
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import WeilConjectures.SixFunctors.OpenClosed.Exact
import Sheaf.Paper.RingedDerivedSliceLocalization
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.AlgebraicGeometry.Morphisms.QuasiFiniteFactorization
import Sheaf.AlgebraicGeometry.BirationalBadLocusComparison
import Sheaf.AlgebraicGeometry.ConstructibleFiniteOpenConstantGeneration
import Sheaf.AlgebraicGeometry.PrimeToEllUniformizationStandardForm
import Sheaf.AlgebraicGeometry.RegularNormalCrossingsConstantImage
import Sheaf.CategoryTheory.ThickVerdierQuotientKernel

/-!
# Gabber finiteness for an open immersion

Source: Illusie--Laszlo--Orgogozo, Expose XIII, Theorem 1.1.1
(blueprint: lem-per-gabber-open-immersion-sheaf-finiteness).

The statement records constructibility and eventual vanishing of the cohomology sheaves of the
right-derived direct image of a constructible finite-field module sheaf along an open immersion
into a Noetherian quasi-excellent scheme on which the coefficient characteristic is invertible.

Proof: apply the codimension induction and finite-generation argument of ILO XIII, §§3.1--3.7,
using the statement dependencies recorded in the DAG. The resulting derived direct image has
constructible cohomology in every degree and is bounded above; a bounded-below injective
resolution gives the lower bound. -/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Gabber finiteness for an open immersion with constructible finite-field input.

Source: Illusie--Laszlo--Orgogozo, Expose XIII, Theorem 1.1.1 and Sections 3.1--3.7;
Bhatt--Scholze, Theorem 6.7.1 with coefficient ring B and maximal ideal zero
(blueprint: lem-per-gabber-open-immersion-sheaf-finiteness).

Proof (the DAG's codimension-induction argument):
1. Throughout, $D^b_c$ has the meaning of [def-weil-pbc-constructible-complexes]. It is closed
   under shifts, finite direct sums, retracts and distinguished triangles: in the long exact
   cohomology sequence, each cohomology is an extension of a kernel by a cokernel; these are
   constructible by [thm-constructible-serre]. Finitely many bounded intervals have a common
   finite bound. Right-derived direct image is triangulated by
   [lem-pc-right-derived-functor-triangulated]. The triangles of
   [lem-sf-derived-truncation-triangle], applied successively to a bounded interval of cohomology,
   therefore reduce assertions about bounded constructible input complexes to their cohomology
   sheaves, without requiring a bound uniform in the sheaf. For later use, a finite map has exact
   direct image on abelian sheaves by [lemma-weil-pbc-finite-direct-image-exact]. The comparison
   [lem-sbc-higher-direct-image-forget-comparison] implies vanishing of its higher module direct
   images too. Its degree-zero direct image preserves constructibility by
   [lem-weil-pbc-finite-fp-pushforward-constructible]; here finite maps between Noetherian schemes
   are finitely presented by [pqf-lem-lft-fp-locnoeth]. Thus finite direct image preserves
   $D^b_c$.
2. For each $c\geq0$, prove simultaneously for all Noetherian quasi-excellent $X$ with $\ell$
   invertible, all open immersions $j:V\hookrightarrow X$ and all $K\in D^b_c(V,B)$ the assertion
   $P_c$: there is a closed $C\subseteq X$ with every point of height $>c$ such that $Rj_*K$ is
   bounded constructible on $X\setminus C$. Height means $\dim\mathcal O_{X,x}$. Noetherian and
   quasi-excellent hypotheses persist under finite-type maps, closed subschemes and open
   restrictions by [lem-per-quasi-excellent-finite-type-stability]. Derived restriction to a
   target open or etale object commutes with direct image, with its adjunction maps, by
   [lem-weil-pbc-ringed-derived-slice-localization]. For $c=0$, take $C=\overline V\setminus V$:
   it contains no generic point of an irreducible component of $X$, and hence all its points have
   positive height. On $V$, the direct image restricts to $K$; on $X\setminus\overline V$ it is
   zero. These two disjoint opens are $X\setminus C$, proving $P_0$. Fix $c\geq1$ and assume
   $P_{c-1}$ for all these schemes and complexes, not just the current pair.
3. First establish the constant-input case of $P_c$ for an integral $X$ and a nonempty (hence
   dense) open $j:V\hookrightarrow X$. By $P_{c-1}$ choose a bad closed set $C$ whose points have
   height at least $c$. It has finitely many irreducible components. Components of height $>c$ can
   be left in the new bad set. It suffices to prove bounded constructibility near the generic
   point $t$ of each height-$c$ component $T$: remove the other components temporarily so that
   $Rj_*B_V$ is good on $X\setminus T$. Once such neighbourhoods are found, their union with
   $X\setminus C$ is an open good locus; its closed complement contains no point of height $\leq
   c$. Indeed any strict specialization of a height-$c$ generic point has height at least $c+1$,
   by appending one prime to a chain. All changes here are open restrictions, justified by Step 2.
4. Choose the diagram $W_i\xrightarrow{a_i}E_i\xrightarrow{e_i}X'\xrightarrow p X$ and $W_i\to
   Y=\coprod_bY_b$ of [lem-per-prime-to-ell-uniformization-standard-form], for $(X,V)$. Apply
   [lem-per-birational-bad-locus-comparison] to $K=B_V$ and to $P_{c-1}$. Its hypotheses are
   exactly the integral pair, the proper birational $p$, the completely decomposed etale family,
   and the bad component of height $c$ isolated in Step 3. After shrinking around $t$ it supplies
   $T'=\coprod_\alpha T'_\alpha$ finite over $T$, the sections $s_\alpha:T'_\alpha\to
   E_{i_\alpha}$, and a map $$A=(Rj_*B_V)|_T\longrightarrow C_1=(p_T)_*((Rj'_*B_{V'})|_{T'})$$
   whose cone is bounded constructible. All schemes in the diagram are Noetherian and
   quasi-excellent by the stability cited in Step 2. It remains to show $C_1\in D^b_c(T,B)$.
5. Fix $\alpha$ and abbreviate $E=E_{i_\alpha}$, $a:W=W_{i_\alpha}\to E$, $r=r_{i_\alpha}$, and
   $S=T'_\alpha$. Let $V_E,V_W$ be the inverse images of $V$, with open inclusions $j_E,j_W$. The
   trace of [lem-pur-quasifinite-flat-weighted-trace] for $a|_{V_E}$ has composite $B_{V_E}\to
   a_*B_{V_W}\to B_{V_E}$ equal to multiplication by $r$. Since $\ell\nmid r$, multiply the trace
   by $r^{-1}\in B$ to split the unit. Apply $Rj_{E*}$ and use
   [lem-cbc-etale-derived-direct-image-coherence] and finite exactness from Step 1: this makes
   $Rj_{E*}B_{V_E}$ a retract of $a_*Rj_{W*}B_{V_W}$. Pull back along $s_\alpha:S\to E$. Proper
   base change for the finite $a$ is [det-properbasechange-modules], giving
   $$s_\alpha^*a_*Rj_{W*}B_{V_W}\simeq(a_S)_*((Rj_{W*}B_{V_W})|_{W\times_E S}).$$ Here all
   coefficients are killed by $\ell$, so the torsion hypothesis is satisfied. Etale slice
   localization from Step 2 identifies $s_\alpha^*Rj_{E*}B_{V_E}$ with $(Rj'_*B_{V'})|_S$ because
   $e_{i_\alpha}s_\alpha:S\to X'$ is the inclusion. Thus this last complex is a retract of the
   displayed finite direct image.
6. Write $g:A\to C_1$ for Step 4 and let $C_3$ be the finite sum over $\alpha$ of the complexes in
   Step 5 pushed to $T$. That step supplies $u:C_1\to C_3$ and a normalized trace $v:C_3\to C_1$
   with $vu=1$. Put $S'''_\alpha=W_{i_\alpha}\times_{E_{i_\alpha}}T'_\alpha$ and
   $b_\alpha:S'''_\alpha\to T$; these maps are finite. Let $h_\alpha:S'''_\alpha\to Y$ be the
   given maps. By [lem-per-regular-normal-crossings-constant-image], $Rj_{Y*}B_{V_Y}\in
   D^b_c(Y,B)$, so $$D=\bigoplus_\alpha(b_\alpha)_*h_\alpha^*Rj_{Y*}B_{V_Y}\in D^b_c(T,B).$$
   Pullback is exact by [prop-weil-pbc-inverse-image-modules-exact], so commutes with cohomology
   and preserves its bounds. Pulling back a finite stratification and its finite locally constant
   restrictions preserves constructibility by [lem-weil-pbc-constructible-etale-set-pullback],
   applied to the underlying abelian sheaves; finite direct image preserves it by Step 1. The
   canonical base-change units give maps $d:A\to D$ and $w:D\to C_3$. The two chains $W_i\to
   E_i\to X'\to X$ and $W_i\to Y\to X$ have the same composite. The composition formula of
   [lem-fin-module-exchange-composite-base-change], applied to the open $j$ along these two chains
   and then restricted to $S'''_\alpha$, therefore gives the explicit equality $wd=ug$. It uses no
   invertibility of base change along $W_i\to Y$. Consequently $g=vug=vwd$ factors through $D$.
7. Apply [lem-per-thick-verdier-quotient-kernel] to $D^+(T_{\mathrm{et}},B)$ and its thick
   subcategory $D^b_c(T,B)$, whose closure properties were proved in Step 1. The cone of $g:A\to
   C_1$ is in this subcategory, so $Q(g)$ is an isomorphism. Step 6 factors $g$ through $D\in
   D^b_c$, so $Q(g)=0$. An invertible zero map has zero source: its inverse composed with it is
   the identity and is zero. Thus $Q(A)=0$, and the kernel criterion gives $A\in D^b_c(T,B)$. If
   $T'$ is empty, Step 4 already has zero target and the same argument applies. Together with
   bounded constructibility off $T$, this proves it on the neighbourhood of $t$: combine the two
   finite stratifications, one on $T$ and one on its open complement, and take the maximum of
   their bounds. Step 3 now proves $P_c$ for constant input on every integral $X$.
8. It remains to prove $P_c$ for all input sheaves and all $X$. For fixed $j:V\hookrightarrow X$,
   the class of constructible sheaves satisfying it is stable under finite sums, extensions and
   retracts: take a finite union of their bad closed sets, and apply Step 1 on its complement. By
   [lem-per-constructible-finite-open-constant-generation], it is enough to treat $\pi_*k_!B_W$
   with $\pi:V'\to V$ finite, $V'$ integral, and $k:W\hookrightarrow V'$ nonempty open. Apply
   [thm-pqf-zmt-factorization] to the separated quasi-finite finite-type map $V'\to X$, obtaining
   $V'\xrightarrow{j'}X'\xrightarrow{\bar\pi}X$ with $\bar\pi$ finite. Replace $X'$ by the reduced
   closure of $V'$; its intersection with the open $V'$ is unchanged because $V'$ is reduced, so
   $X'$ is integral and $V'$ is dense in it. It remains Noetherian quasi-excellent by Step 2. By
   [lem-cbc-etale-derived-direct-image-coherence] and finite exactness,
   $$Rj_*\pi_*k_!B_W\simeq\bar\pi_*Rj'_*k_!B_W.$$ Thus we must first find the desired good locus
   for the rightmost open direct image on the integral scheme $X'$.
9. Let $i:H=V'\setminus W\hookrightarrow V'$ be the reduced closed complement. The sequence of
   [lem-weil-pbc-open-closed-short-exact] gives the triangle $k_!B_W\to B_{V'}\to i_*B_H\to$. By
   Step 7, $Rj'_*B_{V'}$ is good outside a closed subset of height $>c$ in $X'$. Put $\bar
   H=\overline H\subset X'$ with the reduced structure, let $m:H\hookrightarrow\bar H$ be open,
   and $n:\bar H\hookrightarrow X'$ be closed. Composition and finite exactness give
   $$Rj'_*i_*B_H=n_*Rm_*B_H.$$ By $P_{c-1}$ on $\bar H$, the right side is good outside a closed
   subset $C_H\subseteq\bar H$ of height at least $c$ in $\bar H$. Since $X'$ is integral and $W$
   is nonempty, $\bar H$ is a proper closed subset. A prime chain of length $c$ in $\bar H$
   extends to one of length $c+1$ in $X'$ by placing the generic point of $X'$ before it. Thus
   $C_H$ has height $>c$ in $X'$. Outside the union of these two bad sets, the triangle and Step 1
   show $Rj'_*k_!B_W\in D^b_c$. If $H$ is empty, its contribution is zero.
10. Let $C'\subseteq X'$ be the closed bad subset obtained in Step 9. Its image $C=\bar\pi(C')$ is
   closed because $\bar\pi$ is finite. For $x'\in C'$ and $x=\bar\pi(x')$, the local dimension
   inequality [lem-weil-pbc-dimension-inequality-quasi-finite] gives
   $\operatorname{ht}_{X'}(x')\leq\operatorname{ht}_X(x)$, since a finite ring map is quasi-finite
   at every prime. Consequently every point of $C$ has height $>c$. Over $X\setminus C$, the
   finite pushforward in Step 8 comes entirely from $X'\setminus C'$; it is bounded constructible
   by Step 1 and target-open localization in Step 2. This proves $P_c$ for each generator, hence
   for every constructible sheaf by Step 8. Successive truncation triangles from Step 1 prove it
   for every bounded constructible $K$. This completes the induction, with $X$ and $K$ varying at
   each rank.
11. Apply $P_c$ for every $c$ to the original pair $(j,M[0])$. Write $C_c$ for the resulting
   closed subsets and $O_c=T\setminus C_c$ for their good open complements. Each $x\in T$ has
   finite height by [lem-weil-pbc-noetherian-local-finite-krull-dimension] applied to $\mathcal
   O_{T,x}$. Taking $c\geq\operatorname{ht}_T(x)$ forces $x\notin C_c$, so $(O_c)$ covers $T$.
   Quasi-compactness gives a finite subcover. The finitely many cohomological bounds on those
   opens have a common maximum, so $R^qj_*M$ vanishes above that maximum. For each remaining
   degree combine finite constructible stratifications on a finite open subcover: successively
   remove earlier opens from each later one and intersect their strata; these differences and
   intersections are locally closed constructible subsets in the Noetherian space. This gives a
   finite stratification of $T$ with finite locally constant restrictions. Thus every $R^qj_*M$ is
   constructible. Right-derived direct image of a degree-zero sheaf has no negative cohomology;
   take $N_M\geq0$ at least the resulting upper bound. Empty $T$, empty $U$, and $M=0$ give the
   zero complex and $N_M=0$; $j=1_T$ also has this bound. The finite subcover depends on $M$, as
   allowed in the statement. -/
theorem gabber_open_immersion_sheaf_finiteness
    (ell : ℕ) [Fact ell.Prime] (B : Type (u + 1)) [Field B] [Finite B] [CharP B ell]
    {U T : Scheme.{u}} [IsNoetherian T]
    (hT : ∀ V : T.affineOpens, IsQuasiExcellent Γ(T, V.1))
    (hℓ : ∀ t : T, IsUnit (ell : T.presheaf.stalk t))
    (j : U ⟶ T) [IsOpenImmersion j]
    (M : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} B))
    (hM : Scheme.IsConstructibleEtaleModuleSheaf M) :
    (∀ q : ℤ,
      Scheme.IsConstructibleEtaleModuleSheaf
        ((DerivedCategory.Plus.homologyFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) q).obj
          ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} B) j).obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)) 0).obj M)))) ∧
      ∃ N : ℕ, ∀ q : ℤ, (N : ℤ) < q →
        IsZero ((DerivedCategory.Plus.homologyFunctor
          (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} B)) q).obj
          ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} B) j).obj
            ((DerivedCategory.Plus.singleFunctor
              (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} B)) 0).obj M))) := by
  sorry

end AlgebraicGeometry.Etale
