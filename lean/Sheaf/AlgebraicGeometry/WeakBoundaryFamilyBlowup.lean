/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.WeakBoundaryFamily
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Blowup.Gluing
public import WeilConjectures.Compactification.StrictTransform
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Sheaf.RingTheory.BoundaryRegularFlagParameters
import Sheaf.RingTheory.CleanPairSubflagParameters
import Sheaf.AlgebraicGeometry.SNCBoundaryParameterCriterion
import Sheaf.TraceFormula.EtaleRegularIntersectionDescent
import Sheaf.RingTheory.ParameterBlowupCoordinateQuotients
import Sheaf.AlgebraicGeometry.PermissibleCoordinateChart
import WeilConjectures.Blowup.BlowupUniversal
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
import WeilConjectures.Blowup.Complement
import WeilConjectures.Blowup.Proper
import WeilConjectures.Blowup.FlatBaseChange

/-!
# Blowing up minimal intersections of a weak boundary family

Source: ILO, Travaux de Gabber, VIII 4.2.8--4.2.13, printed pp. 120--122;
VI 1.7 for the divisorial log structure
(blueprint: lem-per-weak-boundary-family-blowup).
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
namespace BoundaryFamily

/-- Blow up the distinct minimal nonempty intersections, preserving the weak boundary
property and scheme-theoretic intersections, with the stated exceptional ideal factor.
The first empty-family prefix is a terminating, principalizing tower, bounded by the
intersection-poset height. Its comparisons under family-preserving isomorphisms are
unique, so they respect identities and composition, including permutations.
Source: ILO VIII 4.2.8--4.2.13 and VI 1.7
(blueprint: lem-per-weak-boundary-family-blowup).

Proof plan:
1. Deduplicate the finite collection of nonempty $Y_J$. For two distinct minimal members $V,W$,
the intersection $V\cap W$ is another intersection. If nonempty, minimality forces it to equal
both $V$ and $W$, a contradiction. Thus their scheme-theoretic intersections are empty. Their
union $C$ is consequently a disjoint union of regular closed subschemes. Locally at $C$ only one
of these subschemes occurs, so the assumed normal-crossings parameters for that member are also
parameters for $C$. For any intersection $T=Y_J$ and minimal $V$, the same argument shows $V\cap
T$ is either empty or $V$ (scheme-theoretically). Thus near $V$ either $T$ is absent or
$V\subseteq T$.

2. All centers have finite-type ideals since $X$ is Noetherian. By
[thm-nagata-global-blowup-proper], [def-weil-proper-morphism] and
[lem-weil-pbc-finite-type-over-noetherian], the blowup $X'$ is Noetherian. By
[thm-nagata-global-blowup-complement] it is unchanged away from $C$; strict transforms there are
ordinary pullbacks by [lemma-nagata-strict-transform-restrict]. We may compute near $C$ after
the etale neighborhoods in the hypothesis and localization at their points: etale maps are flat
by [def-weil-etale-morphism], and blowups have the canonical flat base change of
[def-nagata-blowup-flat-base-change-map], [thm-nagata-blowup-flat-base-change]. The closure
defining strict transform commutes with these flat changes: apply
[lemma-nagata-dense-flat-pullback] to the schematically dense open part of its closure
[def-nagata-strict-transform]; its pullback remains dense in the pulled-back closed subscheme.
The open parts are quasi-compact and quasi-separated here because all schemes involved are
Noetherian.

3. Fix a minimal $V$ and a nonempty intersection $T$ containing it. In the local ring $R$ of the
preceding neighborhood, their ideals $P\subseteq Q$ have regular quotients and separately have
normal crossings with the boundary. By [lem-sfb-snc-boundary-parameter-criterion] the ideal of
$B$ in $R$ is $(b_1\cdots b_r)$ for distinct members $b_1,\ldots,b_r$ of a regular system of
parameters (a regular system of parameters of $\mathcal O_{X,x}$ remains one in the etale local
ring $R$, since $R$ is flat and unramified over it). In each of the two parameter systems given
by the hypothesis for $T$ and for $V$, the boundary is a product of distinct parameters $s_j$;
by [lem-sfb-transverse-prime-ideal-parameters](b) the primes minimal over the boundary ideal are
exactly the $(b_i)$ and also exactly the $(s_j)$, and equal principal primes in the domain $R$
have generators differing by a unit. So both systems contain all $b_i$ up to units, which is the
hypothesis of the next lemma. Apply [lem-per-boundary-regular-flag-parameters] to obtain
$P=(t_1,\ldots,t_m)$, $Q=(t_1,\ldots,t_l)$ and boundary a product of selected $t_i$. Here
$l\ge1$ since the center is nowhere dense. The chart with denominator $a=t_i$, $i\le l$, is
$A_i=R[u_j:j\le l,j\ne i]/(t_j-a u_j)$. Apply [lem-trf-permissible-coordinate-chart] with
auxiliary boundary $V(t_1\cdots t_d)$ and the selected original boundary as $H$: its center
condition is satisfied even if the original boundary is empty. In particular $A_i$ is regular
and the reduced inverse image of $B\cup V$ consists of the exceptional hyperplane and the
surviving original boundary hyperplanes. The quotient and local-parameter assertions of
[lem-trf-parameter-blowup-coordinate-quotients] apply to every subset of these coordinates.

4. On that chart, if $i\le m$, the extended ideal of $T$ contains $a$, so the part of $T$ off
the exceptional divisor is empty and its strict transform is empty. Its total ideal is $(a)$,
since $a$ is one of its generators and all other $t_j$ for $j\le m$ are multiples of $a$. If
$i>m$, the total ideal is $a(u_1,\ldots,u_m)$ and the strict-transform ideal is
$(u_1,\ldots,u_m)$. Indeed the quotient by the latter ideal has $a$ as a regular parameter
wherever it vanishes, by [lem-trf-parameter-blowup-coordinate-quotients]; hence it has no
$a$-power torsion. The closure of the localization away from $a$ therefore has exactly this
ideal [def-nagata-strict-transform]. These formulas also cover $m=l$, where every
strict-transform chart is empty, and $m=0$. Thus every surviving strict transform of $T$ is
regular and has normal crossings with the displayed new boundary. This computation is made
separately for each $T$; no simultaneous-coordinate assertion for the entire weak family is
assumed.

5. The preceding equations hold on actual etale neighborhoods of each point of $X'$: the
finitely many parameters and ideal equalities in the local ring extend after shrinking the
neighborhood. Use [lem-trf-etale-regular-intersection-descent] with the empty labelled family to
descend regularity of $X'$, of each strict transform $T^{\mathrm{st}}$, and of the exceptional
divisor separately; no positive-codimension claim is taken from this application. The original
boundary has finitely many irreducible components by [def-trf-strict-normal-crossings-boundary].
A nonempty strict transform of one such component is irreducible, since it is the closure of its
dense open part; if that open part is empty the transform is empty. Distinct surviving
components remain distinct on the complement of the center. Apply
[lem-trf-labelled-coordinate-boundary-globalization] to their strict transforms and to
$E=p^{-1}C$. Its local labelled hyperplanes, regular coordinate intersections, Noetherian
ambient scheme and reducedness hypotheses are supplied by the charts over $C$. At a point of
$X'\setminus E\cong X\setminus C$ they are supplied by
[lem-sfb-snc-boundary-parameter-criterion] for the original $B$, which there equals the reduced
pullback of $B\cup C$: its local ideal is $(t_1\cdots t_r)$ for part of a regular system of
parameters, each surviving component is one of these hyperplanes, and coordinate intersections
are regular of the expected codimension by [lem-sfb-transverse-prime-ideal-parameters](b). It
gives regular $E$ and a strict normal crossings boundary $B'=E\cup B^{\mathrm{st}}$. Finally
[lem-per-regular-boundary-divisorial-chart] gives the required fs divisorial log regular
structure on $(X',B')$.

6. To prove compatibility with intersections it is enough to prove the binary equality
$T^{\mathrm{st}}\cap S^{\mathrm{st}}=(T\cap S)^{\mathrm{st}}$ for two original intersections. It
holds off $C$. Near a minimal $V$, either $T$ or $S$ is absent, or $V\subseteq T\cap S$ by step
1. In the latter case their local ideals $P,Q$ and the ideal $K$ of $V$ satisfy the hypotheses
of [lem-per-clean-pair-subflag-parameters]: all four quotients are regular by the weak-family
assumption. Choose the coordinates provided there, with $K=(t_1,\ldots,t_l)$ and $P,Q$ generated
by subsets $A,B$ of these parameters. On the chart with denominator $t_i$, if $i\in A\cup B$, at
least one of the two strict transforms and the strict transform of their intersection are empty.
If $i\notin A\cup B$, the strict-transform ideals are respectively $(u_a:a\in A)$, $(u_b:b\in
B)$ and $(u_c:c\in A\cup B)$, by the saturation calculation of step 4 and
[lem-trf-parameter-blowup-coordinate-quotients]. Their sum is exactly the third ideal. Induct on
the size of the index subset to obtain $\bigcap_{j\in J}Y_j'=Y_J^{\mathrm{st}}$.

7. For fixed $J$, the minimal centers which meet $Y_J$ are exactly those contained in it, by
step 1. Over these centers, step 4 says $\mathcal I_{Y_J}\mathcal O_{X'}=\mathcal
I_{Y_J^{\mathrm{st}}}\mathcal I_E$; over every other center and away from the center it says
$\mathcal I_{Y_J}\mathcal O_{X'}=\mathcal I_{Y_J^{\mathrm{st}}}$. Therefore these local
equalities glue to the asserted product with the Cartier ideal of the exceptional components
whose images lie in $Y_J$. These components form an open and closed union in $E$: the centers
are disjoint and each is either contained in $Y_J$ or disjoint from it. Regularity and the
Cartier property of this exceptional union follow from the labelled boundary statement in step
5. The intersection equality of step 6 and the regularity/normal crossings of step 4 prove that
the new family has exactly the same weak-boundary property. Each strict transform is still
nowhere dense: its open part off $E$ is nowhere dense there, and the coordinate equations in
step 4 show that it contains no component along $E$.

8. Repeat the one-stage construction just proved. Define the rank of a distinct nonempty
original intersection $T$ to be the maximum number of members of a strict chain ending at $T$ in
the finite intersection poset. We prove by induction on $r$ that every intersection of rank at
most $r$ has empty strict transform after $r$ stages. The claim is trivial for $r=0$. Suppose
all proper sub-intersections of $T$ have disappeared after $r-1$ stages. If a current nonempty
intersection $S'$ is contained in $T'$, step 6 identifies $S'$ with the transform of $S\cap T$.
If $S\cap T$ is properly contained in $T$, the induction hypothesis makes it empty, a
contradiction. Otherwise $S\cap T=T$, so $S'=T'$. Thus any nonempty $T'$ of rank $r$ is minimal
in the current family and is the center of that stage; its next strict transform is empty (step
4). The maximum rank bounds termination. There are at most $2^{|I|}-1$ nonempty indexed
intersections, and any strict chain has length at most $|I|$ by successively dropping indices.
In particular the bound requested for an intersection-closed family with at most $|I|$ distinct
members holds. Disconnected strata can disappear early, so equality with the global poset height
is not asserted.

9. Track every original ideal along this induction. Initially $\mathcal I_{Y_J}=\mathcal
I_{Y_J}\mathcal O_X$. If at stage $n$ its total ideal is $\mathcal I_{Y_{n,J}}\mathcal L_{J,n}$
with $\mathcal L_{J,n}$ an effective Cartier ideal, step 7 factors the pullback of the first
factor as the next strict-transform ideal times the Cartier ideal of the newly selected
exceptional components. The pullback of $\mathcal L_{J,n}$ is effective Cartier by
[lemma-nagata-cartier-total-transform-blowup]. Multiplying these locally principal
non-zero-divisor ideals gives the next Cartier factor. At termination the strict transform is
empty, whose ideal is the unit ideal, so the total-transform ideal is invertible. This also
treats an originally empty $Y_J$ and a center of codimension one.

10. An isomorphism of $X$ preserving the finite indexed family, possibly by permuting its
indices, preserves its scheme-theoretic intersections, equality and inclusion, hence the union
of the distinct minimal nonempty members. It identifies the center ideal and all its powers, and
therefore identifies the graded Rees algebras. Relative Proj sends that graded equivalence to a
blowup isomorphism by [prop-nagata-relative-proj-functoriality]. It also preserves the open
complement and its scheme-theoretic closure, so preserves each strict transform
[def-nagata-strict-transform]. Repeat this argument at every stage. Composing isomorphisms gives
the same graded maps and the same closure identifications, so the tower comparison respects
composition. If the family, or its collection of nonempty intersections, is empty the stopping
rule returns the identity tower of length zero. -/
theorem weak_boundary_family_blowup
    {I : Type v} [Fintype I] (S : BoundaryFamily.{u} I) (hS : S.IsWeak) :
    (∀ V W : S.scheme.IdealSheafData,
      S.IsMinimal V → S.IsMinimal W → V ≠ W → V ⊔ W = ⊤) ∧
    IsRegularWithBoundary S.boundary S.center ∧
    S.step.IsWeak ∧
    IsRegularScheme (S.center.comap S.center.blowupMap).subscheme ∧
    (S.center.comap S.center.blowupMap).IsInvertible ∧
    S.step.HasLogRegularBoundary ∧
    (∀ J : Finset I, J.Nonempty →
      S.step.intersection J = S.transform (S.intersection J) ∧
      (S.exceptionalPart (S.intersection J)).IsInvertible ∧
      (S.intersection J).comap S.center.blowupMap =
        S.transform (S.intersection J) * S.exceptionalPart (S.intersection J)) ∧
    ∃ n : ℕ, n ≤ S.height ∧
      (Nat.card {L : S.scheme.IdealSheafData // S.IsMember L} ≤ Fintype.card I →
        n ≤ Fintype.card I) ∧
      (S.level n).Done ∧
      (∀ k : ℕ, k < n → ¬ (S.level k).Done) ∧
      (S.Done → n = 0) ∧
      (∀ k : ℕ, k ≤ n → (S.level k).IsWeak) ∧
      (∀ k : ℕ, k < n →
        IsRegularWithBoundary (S.level k).boundary (S.level k).center ∧
        IsRegularScheme
          ((S.level k).center.comap (S.level k).center.blowupMap).subscheme ∧
        (S.level (k + 1)).HasLogRegularBoundary) ∧
      (∀ (k : ℕ) (J : Finset I), k ≤ n → J.Nonempty →
        (S.level k).intersection J = S.iteratedTransform (S.intersection J) k) ∧
      (∀ J : Finset I, J.Nonempty →
        S.iteratedTransform (S.intersection J) n = ⊤ ∧
        ((S.intersection J).comap (S.toBase n)).IsInvertible) ∧
      ∀ (K : Type w) [Fintype K] (T : BoundaryFamily.{u} K)
        (σ : K ≃ I) (e : T.scheme ≅ S.scheme), S.PreservesFamily T σ e →
        (T.level n).Done ∧ (∀ k : ℕ, k < n → ¬ (T.level k).Done) ∧
        ∃! E : (k : Fin (n + 1)) → (T.level k.val).scheme ≅ (S.level k.val).scheme,
          E ⟨0, Nat.zero_lt_succ n⟩ = e ∧
          (∀ k : Fin (n + 1), (E k).hom ≫ S.toBase k.val =
            T.toBase k.val ≫ e.hom) ∧
          (∀ k : Fin (n + 1),
            (S.level k.val).PreservesFamily (T.level k.val) σ (E k)) ∧
          (S.boundary.comap e.hom = T.boundary →
            ∀ k : Fin (n + 1),
              (S.level k.val).boundary.comap (E k).hom = (T.level k.val).boundary) ∧
          ∀ k : Fin n,
            (E k.succ).hom ≫ (S.level k.val).center.blowupMap =
              (T.level k.val).center.blowupMap ≫ (E k.castSucc).hom := by
  sorry

end BoundaryFamily
end AlgebraicGeometry
