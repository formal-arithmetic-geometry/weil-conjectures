/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.AlgebraicGeometry.SmoothBaseChangeCoefficients
public import Sheaf.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
import Sheaf.AlgebraicGeometry.FiniteTypeFieldPushforwardEmbedding
import Sheaf.AlgebraicGeometry.FiniteConstructibleDirectImage
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Sheaf.AlgebraicGeometry.FiniteOverProjective
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Curve
import Sheaf.RingTheory.IntegralExtensionDimension
import Sheaf.AlgebraicGeometry.DimensionAffineOpenCover
import Sheaf.AlgebraicGeometry.Dimension
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.AlgebraicGeometry.ProjectiveCurveFiniteGroup
import Sheaf.AlgebraicGeometry.EtaleGrothendieckSpectralSequence
import Sheaf.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import Sheaf.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
import Sheaf.CategoryTheory.CartanEilenbergExists
import Sheaf.CategoryTheory.HypercohomologyFirstPage
import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
import WeilConjectures.SixFunctors.BaseChange.EtaleDerived
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.LeraySpectralSequence

/-!
# Constructible coefficients on the projective line

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/thm-fin-projective-line-constructible.md`,
order 1618 (blueprint: thm-fin-projective-line-constructible).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- Every higher direct image of a constructible finite-coefficient module sheaf along
`ℙ¹_S → S` is constructible when `S` is of finite type over a field and the coefficients
are annihilated by a positive integer invertible in that field. The coefficient convention
is imposed on `Spec k`; invertibility of its constant global section is invertibility in `k`.
The two homogeneous coordinates are indexed by `ULift (Fin 2)`.

Source: blueprint `sec-smooth-purity/sk-prop-sf-cbc/thm-fin-projective-line-constructible.md`,
order 1618 (blueprint: thm-fin-projective-line-constructible).

Proof plan (the node's ten steps):

1. Write $P=\mathbf P^1_S$ and $A=\mathbf Z/N$. Here $k$ is the field in the statement, and $N>0$
annihilates $\Lambda$ and is invertible in $k$. The projection $\pi:P\to S$ is proper by
[lemma-nagata-projective-space-base-change-proper], hence quasi-compact and of finite type by
[def-weil-proper-morphism]. It is projective in [def-pc-projective-morphism]: take the identity
closed immersion into $\mathbf P^1_S$. A field is Noetherian because its only ideals are zero and
the whole field, so [lem-weil-pbc-finite-type-over-noetherian] shows that $S$ and then $P$ are
Noetherian. Also $P$ is of finite type over $k$: by
[lem-weil-pbc-projective-space-standard-charts](a),(c), on the two projective-line charts over a
finite affine cover of $S$, its coordinate algebras are $B[t]$ with $B$ finitely generated over
$k$. Choose a finite affine open cover $S=\bigcup_{j=1}^t U_j$. For Steps 2–9, replace $S$ by one
$U_j$, $P$ by $\mathbf P^1_{U_j}$ using [lemma-nagata-projective-space-base-change-pullback], and
$F$ by its restriction. Each $U_j$ is of finite type over $k$ (the finite-type condition is local
on the source and an affine scheme is quasi-compact), and is Noetherian by the same lemma.
Restricting the finite stratification and its local module trivializations preserves
constructibility. Step 10 identifies these local higher direct images and assembles their finite
stratifications on the original $S$.

2. Forget the $\Lambda$-action on $F$ to the canonical $A$-action. The finite locally constant
module trivializations in [def-weil-pbc-constructible-complexes] remain trivializations after this
forgetting, so $F$ is constructible over $A$. Put $Q_0=F$. Inductively apply
[lem-fin-finite-type-pushforward-embedding] to $Q_a$, obtaining an injection $Q_a\hookrightarrow
G^a=\bigoplus_i(h_{ai})_*\underline{M_{ai}}$, with finitely many finite $h_{ai}:Y_{ai}\to P$ and
finite abelian groups $M_{ai}$ killed by $N$. Constant finite $A$-sheaves are constructible.
[lem-fin-finite-morphism] and repeated extensions in [thm-constructible-serre] make $G^a$
constructible; the cokernel clause makes $Q_{a+1}=\operatorname{coker}(Q_a\to G^a)$ constructible,
which justifies the next induction step. Define $d^a$ as the quotient $G^a\to Q_{a+1}$ followed by
the chosen injection $Q_{a+1}\to G^{a+1}$. Then $\ker d^a=Q_a=\operatorname{im}d^{a-1}$ (and $\ker
d^0=F$), so $F[0]\to G^\bullet$ is a quasi-isomorphism of nonnegative complexes.

3. For each $h=h_{ai}$, [lem-fin-finite-over-projective] applies over the affine Noetherian base
now in force, since $P\to S$ is projective, and yields projectivity of $\pi h:Y_{ai}\to S$.
Moreover [lem-weil-pbc-finite-morphism-permanence](c) applied to the proper projection shows that
$Y_{ai}\to S$ is proper, hence of finite type. Thus $Y_{ai}$ is of finite type over $k$: finite
affine covers for the two finite-type maps give coordinate algebras generated by the generators of
the first algebra and the generators of the second algebra. No separatedness of
$S\to\operatorname{Spec}k$ is needed.

4. For a geometric point $\bar s$ with algebraically closed residue field $K$,
[lemma-nagata-projective-space-base-change-pullback] identifies $P_{\bar s}$ with $\mathbf P^1_K$,
whose dimension is at most one by [lem-weil-pbc-p1-field-dimension-one]. By
[lem-weil-pbc-finite-morphism-permanence](a),(b), $h_{\bar s}$ is finite and the inverse images of
an affine open cover of $\mathbf P^1_K$ are affine. Its coordinate maps are integral by
[pqf-lem-finite-integral-lft]. Each source coordinate ring therefore has dimension at most that of
its target coordinate ring by [lem-weil-pbc-integral-extension-dimension]. The affine-cover
formula [lem-pc-dimension-affine-open-cover], together with [lem-pc-scheme-dimension-local-rings]
identifying its local-ring convention with topological dimension, shows that the target chart
rings have dimension at most one and the source fibre has dimension at most one. If the source
fibre is empty the dimension is $-\infty$ and the bound holds directly. This proves the required
bound for every geometric fibre, including nonreduced and disconnected ones.

5. The additive left exact functor $\pi_*$ in [lem-weil-pbc-module-direct-image-left-exact]
commutes with finite sums, which in an abelian category are finite products. The same is true of
$R^b\pi_*$: use [lem-weil-pbc-module-sheaves-enough-injectives] to take injective resolutions of
the finitely many summands, and take their degreewise sum. A finite sum of injectives is
injective, since a map into it extends component by component across a monomorphism; finite sums
preserve exact sequences, since they are computed component by component. Applying $\pi_*$ to this
summed resolution and taking kernels modulo images therefore gives the sum of the individual
$R^b\pi_*$.

6. Each finite group $M=M_{ai}$ has order invertible in $k$: choosing finitely many generators
gives a surjection $A^r\twoheadrightarrow M$, so counting the equal-sized fibres gives $|M|\mid
N^r$. All primes dividing $|M|$ thus divide $N$. By Steps 3 and 4,
[cor-fin-projective-curve-finite-group] applies to $\pi h$ and makes every $R^b(\pi h)_*\underline
M$ constructible as an abelian sheaf. In the composition spectral sequence
[lem-weil-pbc-grothendieck-spectral-sequence] for $h$ and $\pi$ with coefficients $A$,
[lem-fin-finite-morphism] kills all rows $R^c h_*\underline M$ with $c>0$. Its sole row and its
filtration give $R^b\pi_*(h_*\underline M)\cong R^b(\pi h)_*\underline M$. Apply
[lem-sbc-higher-direct-image-forget-comparison] with coefficient rings $A$ and $\mathbf Z$ to
identify the underlying abelian sheaves on the right. A finite locally constant abelian sheaf
killed by $N$ is finite locally constant over $A$: its $A$-action is the unique action given by
repeated addition. Thus the right sides are constructible $A$-sheaves. Step 5 and the extension
clause of [thm-constructible-serre] now make $R^b\pi_*G^a$ constructible for all $a,b\ge0$.

7. Work in $\Mod(P_{\Et},A)$ and $\Mod(S_{\Et},A)$, which are Grothendieck abelian by
[lem-weil-pbc-module-sheaves-grothendieck-abelian], and use the additive left exact functor
$\pi_*$ of [lem-weil-pbc-module-direct-image-left-exact]. Enough injectives are supplied by
[lem-weil-pbc-module-sheaves-enough-injectives]. Apply [lem-sp-cartan-eilenberg-exists] to the
nonnegative complex $G^\bullet$  to obtain $I^{a,b}$, with $a$ the complex degree and $b$ the
resolution degree. Set $J^{b,a}=I^{a,b}$ and exchange the horizontal and vertical differentials;
use the signed row-cohomology identification $(-1)^{ab}$ specified in [thm-sp-if-e1]. Then
$J^{\bullet,a}$ resolves $G^a$, and its column-cohomology complexes resolve $H^a(G^\bullet)$,
exactly the row convention required there. That theorem yields
$E_1^{b,a}=R^b\pi_*G^a\Longrightarrow H^{a+b}(R\pi_*G^\bullet)=R^{a+b}\pi_*F$, with $a,b\ge0$; the
last equality uses the quasi-isomorphism from Step 2 and the definition of the derived direct
image. The first-quadrant double-complex convergence and finite-filtration assertions are those of
[thm-sp-double-complex-spectral-sequences].

8. All $E_1$ entries are constructible by Step 6. If a page is constructible, the kernel, image (a
cokernel of a kernel), and quotient descriptions of the next page make that page constructible by
[thm-constructible-serre]. For each fixed entry, the first-quadrant stabilization in
[thm-sp-double-complex-spectral-sequences] reaches a stable page after finitely many steps. For
fixed total degree $n\ge0$, its abutment has a finite filtration with graded pieces
$E_\infty^{b,a}$ for $a+b=n$. Starting at the zero end of that filtration, the extension clause of
[thm-constructible-serre] proves constructibility of each successive filtered piece and hence
$R^n\pi_*F$ as an $A$-sheaf.  For a sheaf in degree zero choose its injective resolution in
degrees $0,1,\ldots$ as in [def-weil-pbc-direct-image]; applying $\pi_*$ leaves all negative terms
zero, so negative cohomology vanishes.

9. Finally [lem-sbc-higher-direct-image-forget-comparison], applied once to the original
$\Lambda$-sheaf and once to its underlying $A$-sheaf, identifies the underlying abelian sheaves of
both higher direct images. Their common abelian sheaf is constructible by Step 8. On any of its
finite locally constant strata from [def-weil-pbc-constructible-complexes], choose an etale cover
trivializing it as the finite abelian group $M$. At each geometric point, refine this cover so the
endomorphism for every $\lambda\in\Lambda$ has a fixed value on every $m\in M$: an equality of two
germs of sections holds on a neighbourhood, and there are only finitely many pairs $(\lambda,m)$.
On this refinement all action tables are constant. The module identities are already sheaf
identities, so the fixed table makes $M$ a finite $\Lambda$-module and the trivialization is
$\Lambda$-linear. These neighbourhoods cover the stratum, giving finite local constancy as
$\Lambda$-modules. The same finite stratification therefore proves the required constructibility
of every $R^q\pi_*F$ over $\Lambda$. This uses only ordinary small-etale categories and makes no
assertion for adic coefficients.

10. Return to the original base $S$. For each affine open $j:U_j\hookrightarrow S$,
[lem-weil-pbc-etale-localization-exchange] applied to the underlying abelian sheaf gives
$(R^q\pi_*F)_{ab}|_{U_j}\cong R^q\pi_{j*}(F_{ab}|_{\mathbf P^1_{U_j}})$. The inverse image here is
restriction to the localized site, so it is exact and commutes with kernels, images and
cohomology. By [lem-sbc-higher-direct-image-forget-comparison], the abelian sheaves on the right
underlie the constructible module sheaves proved in Steps 2–9. The finite scalar-action argument
of Step 9 therefore makes the original $R^q\pi_*F$ constructible on each $U_j$. To obtain a finite
partition on $S$, take each local stratum in $U_j$ and intersect it with
$U_j\setminus\bigcup_{i<j}U_i$. These sets are disjoint and cover $S$; they are locally closed
constructible in $S$, since their defining sets are locally closed and all schemes here are
Noetherian. Give them the induced subscheme structures. Restricting the local module
trivializations makes every resulting stratum finite locally constant. There are finitely many
opens and finitely many strata per open, so this is the finite stratification required by
[def-weil-pbc-constructible-complexes]. If $S$ is empty, the empty partition proves
constructibility directly.
-/
theorem isConstructibleEtaleModuleSheaf_higherDirectImage_projectiveLine
    (k : Type u) [Field k] (S : Scheme.{u}) [S.Over (Spec (.of k))]
    [LocallyOfFiniteType (S ↘ Spec (.of k))] [QuasiCompact (S ↘ Spec (.of k))]
    (N : ℕ) (Λ : Type (u + 1)) [CommRing Λ]
    (hcoeff : IsSmoothBaseChangeCoefficients N Λ (Spec (.of k)))
    (F : Sheaf (ProjectiveSpace (ULift.{u} (Fin 2)) S).smallEtaleTopology
      (ModuleCat.{u + 1} Λ))
    (hF : @Scheme.IsConstructibleEtaleModuleSheaf
      (ProjectiveSpace (ULift.{u} (Fin 2)) S) Λ _ hcoeff.2.1 F) (q : ℤ) :
    @Scheme.IsConstructibleEtaleModuleSheaf S Λ _ hcoeff.2.1
      ((DerivedCategory.Plus.homologyFunctor
        (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) q).obj
        ((rightDerivedLowerStarPlus (ModuleCat.{u + 1} Λ)
          (ProjectiveSpace (ULift.{u} (Fin 2)) S ↘ S)).obj
          ((DerivedCategory.Plus.singleFunctor
            (Sheaf (ProjectiveSpace (ULift.{u} (Fin 2)) S).smallEtaleTopology
              (ModuleCat.{u + 1} Λ)) 0).obj F))) := by
  sorry

end AlgebraicGeometry.Etale
