/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.TraceFormula.BoundedConstructibleTransport
public import Sheaf.Paper.OrientedConstructibleSheafVanishing
public import Sheaf.Paper.OrientedNearbyCycles
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap


import Sheaf.Paper.OrgogozoInductionData
import Sheaf.AlgebraicGeometry.NagataAffineOpensProjective
import Sheaf.AlgebraicGeometry.FiniteTypeFibreDimensionBound
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.Paper.AlterationFiniteRefinement
import Sheaf.Paper.ModificationClosedImageLifting
import Sheaf.Paper.ModificationsZariskiRefinement
import Sheaf.Paper.NearbyCyclesDimensionBound
import Sheaf.Paper.NearbyFiniteBaseDescent
import Sheaf.Paper.NearbySpreadOut
import Sheaf.Paper.OrgogozoGoodModification
import Sheaf.Paper.OrientedClosedBaseExtension
import Sheaf.Paper.OrientedConstructibleSubquotients
import Sheaf.Paper.OrientedNearbyHypercoverSpectralSequence
import Sheaf.Paper.OrientedProperImageConstructibility
import Sheaf.Paper.PlurinodalProperHypercover
import Sheaf.Paper.PsiConstructibilityDescent
import Sheaf.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.CategoryTheory.RightDerivedFunctorTruncationIso
import Sheaf.AlgebraicGeometry.EtaleProperDirectImageFiniteness
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.TruncationTriangle
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineSpace
import WeilConjectures.SixFunctors.Finite.Exact
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Sheaf.Paper.OrientedSourceLocalization
import Sheaf.TraceFormula.OrientedNearbySmoothSourcePullback

/-!
# Proper-surjective local constructibility of nearby-cycle cohomology

Source: Lu--Zheng, Duality and nearby cycles over general bases, arXiv:1712.10216v7,
proof of Theorem 4.27(2), printed p. 37, last sentence applying Orgogozo Theorem 8.1;
Orgogozo author draft, Theorem 7.1 and Section 9 (blueprint:
lem-trf-psi-proper-surjective-constructibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.OrientedNearbyCycles
open AlgebraicGeometry.OrientedConstructibleSheaf

namespace AlgebraicGeometry.OrientedNearbyCycles

/-- For a bounded constructible complex on a finite-presentation family over a Noetherian
base, each nonnegative nearby-cycle cohomology sheaf becomes constructible after a proper
surjective base change. The nearby cycles are those of the base-changed family itself;
no comparison with the original nearby cycles is included.
Source: Lu--Zheng, proof of Theorem 4.27(2), printed p. 37, and Orgogozo author draft,
Theorem 7.1 and Section 9 (blueprint: lem-trf-psi-proper-surjective-constructibility).

Proof plan, following the recorded DAG steps:
1. There are finitely many irreducible components of $S$ by
[lem-weil-pbc-noetherian-finitely-many-components]. Give them reduced structures $S_i$. Each
$S_i\to S$ is a closed immersion and hence finite, thus proper by [lem-weil-pbc-finite-proper],
and their finite disjoint union is surjective. It suffices to construct the claimed cover
separately over each integral $S_i$: composing the covers with $S_i\to S$ and taking their
disjoint union gives a proper surjection. Both the new family and its vanishing topos decompose
over these open-and-closed components, so the finite-stratification definition
[def-trf-oriented-constructible-sheaf] gives the result componentwise. No comparison with the
nearby cycles over $S$ is needed. We therefore work over an integral base until the last step.

2. For an integral affine base use [lem-trf-nearby-spread-out] to write $(X\to S,K)$ as the
pullback of $(X_0\to S_0,K_0)$, with $S_0$ integral affine of finite type over $\mathbf Z[1/m]$
and $K_0$ bounded constructible. We will first prove the assertion over such arithmetic bases and
their finite-type modifications/alterations, which are excellent Noetherian of finite dimension.
Steps 3--16 do this. Steps 17--18 return to $S$ and then glue finitely many affine opens. The
spread-out assertion alone is not being used to transfer constructibility: the transfer at the end
uses full $\Psi$-goodness and its actual comparison.

3. On the arithmetic schemes fix the lexicographic induction $(\delta,r,d)$: $\delta$ bounds the
dimension of the integral base, $r\geq-1$ is the truncation degree, and $d$ bounds the geometric
fibre dimension of a proper map. The assertion is that every bounded constructible input in
$D^{\geq0}$ acquires constructible $\tau_{\leq r}R\Psi$ after a modification; we may require the
new pair to be $\Psi$-good by [lem-trf-orgogozo-good-modification]. Module sheaves on these small
sites are Grothendieck [prop-pur-kinjective-resolutions-exist]. Right derived direct image is left
t-exact [lem-weil-pbc-derived-functor-negative-vanishing], so $r=-1$ is immediate. Every time a
constructibility assertion has been obtained, first arrange goodness by that theorem if necessary;
exact pullback and the comparison then preserve it under any further base change. Thus finitely
many successful modifications can be combined by [lem-trf-modifications-zariski-refinement]. We
prove the proper case for every $d$ at fixed $(\delta,r)$ before passing to arbitrary finite-type
maps at that same pair of parameters.

4. An alteration suffices at any induction stage. Start with a good pair on an integral base,
using [lem-trf-orgogozo-good-modification]. If $T\to S$ is an alteration on which the relevant
cohomology is constructible, apply [lem-trf-alteration-finite-refinement] to get modifications
$\widetilde T\to T$ and $S'\to S$ and a finite surjection $\widetilde T\to S'$. Goodness of the
original pair identifies the nearby cycles on these bases with pullbacks; hence the good sheaf on
$S'$ pulls back to a constructible sheaf on $\widetilde T$. Apply
[lem-trf-psi-constructibility-descent] to each degree. This produces a modification of $S$ with
the desired truncation. The same reasoning applies when finitely many extra modifications on $T$
were needed. Pullback preserves constructibility here directly: pull back the finite source and
base strata, and pull back their finite locally constant module sheaves
[def-trf-oriented-constructible-sheaf].

5. The finite-type assertion follows once the proper assertion at $(\delta,r)$ is known for all
$d$. Work on an affine open of the base and a finite affine open cover of the source. An affine
finite-type source embeds in affine space and has a dense projective compactification by
[lemma-nagata-quasi-affine-immersion-affine-space-exists] and
[det-nagata-affine-opens-projective]. Extend its bounded constructible complex by $j_!$; this is
exact [lem-weil-pbc-extension-by-zero-exact] and constructible, since its strata are the old
strata and the complementary closed subset, where its stalks are zero
[lem-weil-pbc-extension-by-zero-stalks]. Apply the proper assertion for some fibre bound
[lem-fin-finite-type-fibre-dimension-bound]. Smooth source exchange for the open immersion
[lem-trf-oriented-nearby-smooth-source-pullback] restricts the resulting nearby cycles to the
original family. The open source subtopoi cover the vanishing topos
[lem-trf-oriented-source-localization]. A finite refinement of their strata yields
constructibility globally; common modifications exist by
[lem-trf-modifications-zariski-refinement]. There is no requirement that compactification preserve
$d$: all $d$ have already been proved.

6. For a proper map, reduce bounded nonnegative complexes to sheaves. Successive truncation
triangles [lem-weil-pbc-truncation-triangle] express $K$ through its finitely many constructible
$H^aK[-a]$, $a\geq0$. For $a>0$, degrees through $r$ of $R\Psi(H^aK[-a])$ use only degrees through
$r-a$ of $R\Psi H^aK$, already covered by the lower-$r$ induction. Only the sheaf $H^0K$ requires
the current degree. The long exact cohomology sequences and closure under subquotients and
extensions on the vanishing topos [lem-trf-oriented-constructible-subquotients] finish this
reduction. Triangulatedness and left t-exactness of $R\Psi$ are supplied by
[lem-pc-right-derived-functor-triangulated] and [lem-weil-pbc-derived-functor-negative-vanishing];
all earlier truncations can be kept on common refinements as in Steps 3--4.

7. For a constructible sheaf $E$, [lem-weil-pbc-constructible-module-finite-pushforward-embedding]
supplies $0\to E\to E'\to Q\to0$ with $E'=\bigoplus p_{i,*}\underline{M_i}$, $p_i$ finite and
$M_i$ finite modules. Ordinary proper-image finiteness
[lem-weil-pbc-etale-proper-direct-image-finiteness] (fibre bound zero) makes $E'$ constructible,
so $Q$ is constructible by [thm-constructible-serre]. Lower-$r$ induction handles $Q$. In
[def-trf-oriented-nearby-cycles], $\bar p_i\psi_{fp_i}=\psi_f p_i$; derived composition
[lem-weil-pbc-ringed-topoi-derived-pushforward-composition] therefore gives $R\Psi_f
Rp_{i,*}=R\bar p_{i,*}R\Psi_{fp_i}$. Finite ordinary direct image is exact
[lemma-weil-pbc-finite-direct-image-exact] (forget scalars to test exactness), and finite oriented
direct image is exact [lem-trf-oriented-proper-image-constructibility]. Thus the constant-module
case makes $H^{\leq r}R\Psi E'$ constructible. The exact sequence $H^{j-1}R\Psi Q\to H^jR\Psi E\to
H^jR\Psi E'$ and [lem-trf-oriented-constructible-subquotients] finish for $j\leq r$. Finite $p_i$
preserve the fibre bound. The constants are arbitrary finite modules, not necessarily free.

8. We now prove the proper constant-module case. Cover the source by the finite disjoint union of
its reduced irreducible components, and take its Cech proper hypercover. Its levels are proper
over the original source. In [lem-trf-oriented-nearby-hypercover-spectral-sequence], the terms of
simplicial degree $i>0$ contributing to total degrees at most $r$ require nearby-cycle degrees
only through $r-i<r$; lower-$r$ induction therefore treats them. Applying
[lem-trf-oriented-proper-image-constructibility] to their bounded truncations gives constructible
cohomology after the proper oriented direct images. There are only finitely many relevant
simplicial degrees and the abutment filtration is finite, so
[lem-trf-oriented-constructible-subquotients] finishes once degree zero is treated. Its sources
are integral. This reduction also handles nonreduced sources, without silently replacing a scheme
by its reduction.

9. If the integral proper source does not dominate $S$, it factors through its reduced closed
image $F$, with $\dim F<\delta$. Lower-base-dimension induction on $F$ gives a modification $F'\to
F$ with the required constructibility and goodness. Apply
[lem-trf-modification-closed-image-lifting] to $F'\to S$: after a modification $S'\to S$ there is
a finite surjection $G\to F\times_SS'$ and a map $G\to F'$. Goodness pulls the desired sheaves
from $F'$ to $G$. By [lem-trf-nearby-finite-base-descent] the family over $F\times_SS'$ is good,
and [lem-trf-psi-constructibility-descent] descends its cohomology constructibility from $G$.
Finally [lem-trf-oriented-closed-base-extension] identifies nearby cycles of the proper family
over $S'$ with exact closed extension from $F\times_SS'$, which preserves constructibility. Thus
this case uses strictly smaller $\delta$, regardless of its fibre dimension.

10. For a dominant integral proper source use [lem-trf-plurinodal-proper-hypercover]. After an
integral alteration $T\to S$, its degree-zero source is a finite disjoint union of semistable
towers and a proper source with nowhere dense image. The latter is covered by Steps 8--9. Positive
simplicial degrees of the hypercover are covered by lower-$r$ induction just as in Step 8, using
[lem-trf-oriented-nearby-hypercover-spectral-sequence] and
[lem-trf-oriented-proper-image-constructibility]. Only finitely many levels matter in degrees
through $r$; combine their modifications. It remains to handle the towers in degree zero. Their
lengths equal the generic fibre dimension of the original proper dominant source, hence are at
most $d$. The alteration is converted back to a modification by Step 4 after the tower
calculation. All the alterations here have base dimension $\delta$; the recursion in the positive
levels is in $r$, not an unjustified decrease of source dimension.

11. A tower of length zero is $1_S$. Its nearby cycles of $\underline M$ are $p_2^*\underline M$
by [lem-trf-nearby-smooth-source-exchange], so are constructible and concentrated in degree zero.
For a tower of length $e>0$, write $X\xrightarrow{h}Y\xrightarrow{g}S$, where $h$ is its last
semistable curve and $g$ has fibre dimension $e-1<d$ (or, if $e<d$, use the already proved
lower-$d$ case directly). The datum [def-trf-orgogozo-induction-data] includes a closed
$i:Z\hookrightarrow X$ finite over $Y$ containing the nonsmooth locus; write $j:U=X\setminus
Z\hookrightarrow X$. Set $C=R\Psi_{gh}\underline M$ and $F=H^rC$. Lower-$r$ induction already
makes $\tau_{\leq r-1}C$ constructible. We will show constructibility of $F$ in Steps 12--15.

12. The arithmetic schemes $X$ and $Y$ are Noetherian of finite dimension. For the proper curve
$h$, [lem-weil-pbc-etale-proper-direct-image-finiteness] makes $Rh_*\underline M$ a bounded
nonnegative complex of constructible sheaves (its degrees are $0,1,2$). Lower-$d$ induction for
$g$ therefore applies both to $\underline M$ and to $Rh_*\underline M$, making their nearby cycles
constructible through degree $r$. Arrange their goodness and keep them on a common modification
using [lem-trf-orgogozo-good-modification] and [lem-trf-modifications-zariski-refinement]. The
tower pulls back to a tower. These uses of ordinary proper-image finiteness are on the
finite-dimensional arithmetic schemes only; it is not being applied over the original arbitrary
Noetherian base.

13. On $U$, the last curve is smooth. Smooth source composition
[lem-trf-oriented-nearby-smooth-source-pullback] gives $\bar j^*
C\simeq\overline{h|_U}^{\,*}R\Psi_g\underline M$. Thus $\bar j^*F$ is constructible by Step 12:
exact inverse image pulls back the finite strata and their finite locally constant module sheaves
[def-trf-oriented-constructible-sheaf]. By open/closed source localization
[lem-trf-oriented-source-localization], $A=\bar j_!\bar j^*F$ is a constructible sheaf on
$V_{gh}$. This establishes constructibility on the smooth part without a trait-finiteness theorem.

14. We next show $\bar h_*F$ constructible. Apply $R\bar h_*$ to $\tau_{\leq r-1}C\to\tau_{\leq
r}C\to F[-r]$ [lem-weil-pbc-truncation-triangle], using
[lem-pc-right-derived-functor-triangulated]. The truncation isomorphism
[lem-weil-pbc-derived-functor-truncation-iso] identifies $H^r(R\bar h_*\tau_{\leq r}C)$ with
$H^r(R\bar h_*C)$. The long exact sequence contains $H^r(R\bar h_*C)\to\bar h_*F\to H^{r+1}(R\bar
h_*\tau_{\leq r-1}C)$. Since $\bar h\psi_{gh}=\psi_g h$ [def-trf-oriented-nearby-cycles], the
derived composition isomorphism [lem-weil-pbc-ringed-topoi-derived-pushforward-composition] gives
$R\bar h_*C\simeq R\Psi_g Rh_*\underline M$. Its degree-$r$ sheaf is constructible by Step 12. The
last sheaf is constructible by Step 11 and [lem-trf-oriented-proper-image-constructibility]. Their
images and the resulting extension are constructible by
[lem-trf-oriented-constructible-subquotients], proving the claim. This is the truncation argument
of Lemma 9.3.1, with the actual derived-functor truncation theorem cited.

15. By [lem-trf-oriented-source-localization], $0\to A\to F\to\bar i_*\bar i^*F\to0$ is exact. Set
$\pi=h i:Z\to Y$, which is finite by the tower datum. Applying $R\bar h_*$ gives $\bar h_*A\to\bar
h_*F\to\bar\pi_*\bar i^*F\to R^1\bar h_*A$. Here finite closed direct image is exact
[lem-trf-oriented-proper-image-constructibility], and derived composition
[lem-weil-pbc-ringed-topoi-derived-pushforward-composition] identifies the third term with that
finite pushforward. The outside terms are constructible by that lemma and constructibility of $A$;
the second term is constructible by Step 14. Hence the third is constructible by subquotients and
extensions [lem-trf-oriented-constructible-subquotients]. Finite direct image detects
constructibility [lem-trf-oriented-proper-image-constructibility], so $\bar i^*F$ is
constructible. Exact closed extension and the displayed localization sequence then show $F$
constructible. This finishes the last curve, with no invocation of the theorem being proved.

16. Steps 11--15 prove the tower case needed by Step 10. The finite filtration of
[lem-trf-oriented-nearby-hypercover-spectral-sequence] and
[lem-trf-oriented-constructible-subquotients] then proves the dominant proper constant-module
case. Steps 8--9 prove the other constant-module cases; Steps 6--7 give all bounded nonnegative
constructible inputs. Every recursive call has smaller $\delta$, or smaller $r$, or the same
$(\delta,r)$ with smaller fibre bound $d$. Step 5 extends the conclusion to finite-type maps only
after all proper fibre bounds have been treated. This closes the induction. All combinations
involve finitely many sheaves, hypercover levels and modifications; the unbounded simplicial
object is not being treated by an infinite sequence of alterations.

17. For general bounded $K_0$ on the arithmetic model, shift it into $D^{\geq0}$. A finite bound
$d$ for the fibres exists by [lem-fin-finite-type-fibre-dimension-bound]. If its cohomological
interval after shifting is $[0,b]$, [lem-trf-nearby-dimension-bound] puts its nearby cycles in
$[0,b+2d]$, uniformly after base change. Apply the proved induction with $r=b+2d$, then undo the
shift. We obtain a modification of $S_0$ on which all nearby-cycle cohomology is constructible;
ensure full goodness as well using [lem-trf-orgogozo-good-modification] and a common refinement
[lem-trf-modifications-zariski-refinement]. These further pullbacks preserve the result by
goodness. This bound is used to choose one finite truncation, not as a constructibility theorem.

18. Pull that model modification back to the original integral affine $S$ and take the reduced
closure of its isomorphism open. By [lem-trf-nearby-spread-out] this is a modification $S'\to S$
with a map to the modified model. Full goodness [def-trf-oriented-nearby-cycles] identifies
$R\Psi_{f_{S'}}K_{S'}$ with the inverse image of the model's nearby cycles. This inverse image is
exact, so also identifies each cohomology sheaf. It preserves constructibility: pull back the two
finite stratifications in [def-trf-oriented-constructible-sheaf]; their oriented-product
restrictions carry inverse images of finite locally constant module sheaves. Thus the conclusion
holds over integral affine bases of arbitrary Noetherian dimension. Cover an arbitrary integral
Noetherian $S$ by finitely many affine opens and apply [lem-trf-modifications-zariski-refinement]
to their modifications. Goodness keeps their constructibility on the refinement, and the finite
open covers and finite strata refine to one finite stratification. This proves the integral-base
case.

19. Finally apply the integral-base construction to the finitely many reduced components from Step
1 and take the disjoint union $T$ of the resulting modifications. Its map $p:T\to S$ is proper and
surjective. On each component the cohomology of $R\Psi_{f_T}(p_X^*K)$ is constructible; the
componentwise finite strata combine to finite strata on $X_T$ and $T$, giving constructibility on
$V_{f_T}$ by [def-trf-oriented-constructible-sheaf]. In particular its degree-$q$ cohomology is
constructible for the prescribed $q\geq0$. The proof has established this for the newly
pulled-back family, exactly as stated, using good intermediate pairs only inside the construction.
-/
theorem exists_proper_surjective_constructible
    {X S : Scheme.{u}} [IsLocallyNoetherian S] [CompactSpace S]
    (f : X ⟶ S) [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (m : ℕ) (hm : 1 ≤ m) (hΛ : (m : Λ) = 0)
    (hmS : IsUnit (m : Γ(S, ⊤)))
    (K : EtaleDerived X Λ)
    (hK : IsBoundedConstructible X Λ K)
    (q : ℤ) (hq : 0 ≤ q) :
    ∃ (T : Scheme.{u}) (p : T ⟶ S),
      IsProper p ∧ Surjective p ∧
        IsConstructibleVanishing (pullback.snd f p) Λ
          ((DerivedCategory.homologyFunctor
            ((vanishingDatum (pullback.snd f p)).modules (Coeff Λ)) q).obj
            ((nearbyCycles (pullback.snd f p) Λ).obj
              (((etaleModules (pullback.fst f p)).pull (Coeff Λ)).obj K))) := by
  sorry

end AlgebraicGeometry.OrientedNearbyCycles
