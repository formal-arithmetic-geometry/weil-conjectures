/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q06
-/
module

public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Data.ZMod.Basic

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import WeilConjectures.SixFunctors.Etale.Derived.Triangulated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import Sheaf.AlgebraicGeometry.ExchangeForgetCoefficients
import Sheaf.AlgebraicGeometry.TorAmplitudeKFlatResolution
import Sheaf.CategoryTheory.TruncationsAndHomotopyColimits
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Sheaf.Paper.EtaleKFlatCriteria
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives
import Sheaf.AlgebraicGeometry.EtaleConstantModuleDirectImageLeftExact
import Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Sheaf.Targets.BaseChangeTowardsFields
import Sheaf.AlgebraicGeometry.DerivedOpenRestriction
import Sheaf.AlgebraicGeometry.FibreProductLimit
import Sheaf.AlgebraicGeometry.HigherDirectImagesLimits
import Sheaf.AlgebraicGeometry.ZModSheafInvertibleOrders
import Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleSheafColimit
import Sheaf.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FilteredColimit
import WeilConjectures.Algebra.Homology.FilteredColimitsTensor
import WeilConjectures.AlgebraicGeometry.ConstructibleModuleFinitePushforwardEmbedding
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.SixFunctors.Finite.BaseChange
import Sheaf.AlgebraicGeometry.ProperTorsionProjectionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.GroupTheory.Torsion
import Sheaf.AlgebraicGeometry.DerivedDirectImageComposition
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
import Sheaf.AlgebraicGeometry.DerivedGeometricStalkConservative
import Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison
import Sheaf.AlgebraicGeometry.ArbitrarySchemeUntensoredBaseChange
import Sheaf.AlgebraicGeometry.FinitePushforwardTensorComparison

/-!
# Punctual base change with a tensor factor

Source: Stacks Project, Tag 0F1J, lemma-punctual-base-change-upgrade;
current blueprint sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-0f1j
(blueprint: lem-kun-0f1j).

The comparison is constructed as the mate of the pullback tensor comparison,
the square comparison, and the counit for the lower horizontal morphism.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The canonical tensor base-change map of Stacks Project, Tag 0F1J
(blueprint: lem-kun-0f1j). Its transpose along inverse image by `h` is the tensor
comparison followed by the square identification `h⁻¹ f'⁻¹ ≅ e⁻¹ g⁻¹`, then the
inverse image by `e` of the counit for `g`. This construction requires only a
commutative right square; the theorem below imposes the two cartesian squares. -/
noncomputable def punctualTensorBaseChangeMap
    (Λ : Type (u + 1)) [CommRing Λ] {X X' Y S' T : Scheme.{u}}
    (p : X' ⟶ X) (h : Y ⟶ X') (e : Y ⟶ T) (f' : X' ⟶ S') (g : T ⟶ S')
    (sq : CommSq e h g f') (E : DerivedCategoryModule Λ X) (F : DerivedCategoryModule Λ T) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X').obj
      (L((p)^*[ModuleCat.{u + 1} Λ]).obj E)).obj
        (L((f')^*[ModuleCat.{u + 1} Λ]).obj (R((g)_*[ModuleCat.{u + 1} Λ]).obj F)) ⟶
    R((h)_*[ModuleCat.{u + 1} Λ]).obj
      (((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj
        (L((h)^*[ModuleCat.{u + 1} Λ]).obj (L((p)^*[ModuleCat.{u + 1} Λ]).obj E))).obj
          (L((e)^*[ModuleCat.{u + 1} Λ]).obj F)) :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) h).homEquiv _ _
    ((((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} Λ) h).app
      (L((p)^*[ModuleCat.{u + 1} Λ]).obj E)).app
        (L((f')^*[ModuleCat.{u + 1} Λ]).obj (R((g)_*[ModuleCat.{u + 1} Λ]).obj F))) ≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj
        (L((h)^*[ModuleCat.{u + 1} Λ]).obj (L((p)^*[ModuleCat.{u + 1} Λ]).obj E))).map
          ((derivedSquareUpperStarIso (ModuleCat.{u + 1} Λ) sq).hom.app
            (R((g)_*[ModuleCat.{u + 1} Λ]).obj F)) ≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj
        (L((h)^*[ModuleCat.{u + 1} Λ]).obj (L((p)^*[ModuleCat.{u + 1} Λ]).obj E))).map
          (L((e)^*[ModuleCat.{u + 1} Λ]).map
            ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).counit.app F)))

/-- Punctual base change with a bounded-below tensor factor of lower-bounded Tor amplitude.
Source: Stacks Project, Tag 0F1J (blueprint: lem-kun-0f1j).

Proof plan (the DAG proof, including the refinements of the Stacks reductions):

1. Put $R=\mathbf Z/n\mathbf Z$ and denote the two functors of the statement by $A(E,F)$ and
$B(E,F)$, with comparison $\alpha_{E,F}$. All module categories and sites are taken in a fixed
larger universe, so the filtered diagrams below are small. Inverse image of constant-coefficient
module sheaves is exact by [prop-weil-pbc-inverse-image-modules-exact], and its derived functor is
the termwise functor by [lem-weil-pbc-exact-functor-derived-functor]. Derived tensor is
triangulated in each variable by [lem-kun-derived-tensor-triangulated], and right derived direct
image is triangulated by [lem-pc-right-derived-functor-triangulated]. Consequently $A$ and $B$ are
triangulated in each variable; the counit formula in the statement makes $\alpha$ a natural
transformation compatible with shifts and with the triangles obtained from short exact sequences
of complexes. The inverse-image tensor identifications used here are
[lem-kun-inverse-image-monoidal]. Right direct image preserves a lower cohomological bound: apply
[lem-kun-tensor-t-est] to underlying abelian sheaves and then
[lem-weil-pbc-exchange-forget-coefficients](2) to identify the module direct image. We will use
this lower bound only for right direct image, never for the derived tensor of two arbitrary
cohomologically bounded-below objects. If $n=1$, both coefficient module categories are zero and
the assertion follows immediately.

2. By [lem-kun-0f1m] choose a K-flat flat-term model $\mathcal E^\bullet$ for $E$, zero below $a$,
whose termwise pullbacks are again K-flat and flat-term. Choose $b$ with $F\in D^{\ge b}$. For
$N\ge a$ put $E_N=\sigma_{\le N}\mathcal E$ and $T_N=\sigma_{\ge N+1}\mathcal E$
[def-kun-truncations]. The degreewise split exact sequence $0\to T_N\to\mathcal E\to E_N\to0$
gives a distinguished triangle by [lem-weil-pbc-complex-ses-triangle]. The bounded flat complex
$E_N$ is K-flat by [lem-kun-kflat-criteria](1), as are all its pullbacks. The tails $T_N$ and
their pullbacks are K-flat too: tensor the split sequence with any acyclic complex; it stays
degreewise split exact after totalization, and its middle and last terms are acyclic, so its first
term is acyclic by [lem-weil-pbc-complex-ses-homology-long-exact]. Now represent $F$ and $Rg_*F$
by complexes zero below $b$ using [lem-weil-pbc-dplus-injective-representative]. The K-flat tail
computes each tensor in $A(T_N,F)$ and inside $B(T_N,F)$ by [def-kun-derived-tensor]. Their total
tensor complexes are zero below $N+1+b$; the lower bound from Step 1 gives the same bound after
$Rh_*$. Thus in every degree $q<N+b$ the triangle identifies the map $H^q(\alpha_{E,F})$ with
$H^q(\alpha_{E_N,F})$: both $H^q$ and $H^{q+1}$ of the tail images vanish. For each fixed $q$
choose $N$ large enough. The bounded complex $E_N$ is a finite extension of shifts of its
individual flat terms, using the same stupid-truncation short exact sequences and triangles. It
therefore suffices to prove the assertion for a single flat $R$-module sheaf $\mathcal E$ in
degree zero. The argument establishes the assertion degree by degree; it does not assume
convergence of an infinite filtration.

3. Fix the flat sheaf $\mathcal E$. The complex $\mathcal E[0]$ is K-flat by
[lem-kun-kflat-criteria](1), so its inverse images are flat by
[lem-weil-pbc-ringed-topos-kflat-pullback], applied to this one-term flat complex. Tensor by any
of them is exact [def-pc-flat-sheaf-modules], hence commutes with cohomology by
[lem-weil-pbc-exact-functor-complex-cohomology]. Choose a representative $I$ of $F$ zero below $b$
as in [lem-weil-pbc-dplus-injective-representative]. Set $J_M=\tau_{\le M}I$
[def-kun-truncations], a bounded complex, and $C_M=I/J_M$. This quotient complex is zero below $M$
(its degree-$M$ term is $I^M/\ker d^M$); in particular its cohomology vanishes below $M$. The
exact sequence $0\to J_M\to I\to C_M\to0$ gives a triangle by [lem-weil-pbc-complex-ses-triangle].
Exactness of tensor with the inverse images of $\mathcal E$ and the lower direct-image bound of
Step 1 put $A(\mathcal E,C_M)$ and $B(\mathcal E,C_M)$ in $D^{\ge M}$. For $q<M-1$ the triangle
therefore identifies the comparison for $F$ in degree $q$ with that for $J_M$. Finally the bounded
complex $J_M$ is a finite extension of shifts of its individual sheaf terms, by its
stupid-truncation exact sequences. It suffices to prove $\alpha_{\mathcal E,\mathcal F}$ for every
single sheaf $\mathcal F$; no bounded complex of flat sheaves representing $F$ is assumed.

4. Induct on a positive divisor $m$ of $n$ annihilating $\mathcal F$. For $m=1$ the sheaf is zero.
If $m$ is not prime, choose a prime $\ell\mid m$ and use $0\to\mathcal F[\ell]\to\mathcal
F\to\mathcal F/\mathcal F[\ell]\to0$. The first term is killed by $\ell$, and the last by
$m/\ell$: for a local section $x$, $\ell((m/\ell)x)=mx=0$, so $(m/\ell)x\in\mathcal F[\ell]$. Both
annihilators are smaller than $m$. The associated triangle and Step 1 reduce to prime torsion.
When $\ell\mathcal F=0$, put $k_\ell=\mathbf F_\ell$ and $\overline{\mathcal E}=\mathcal
E/\ell\mathcal E$. For any sheaf $N$ killed by $\ell$, the mutually inverse maps $x\otimes
y\mapsto\bar x\otimes y$ and $\bar x\otimes y\mapsto x\otimes y$ give $\mathcal E\otimes_R
N\cong\overline{\mathcal E}\otimes_{k_\ell}N$: independence of the lift follows from $\ell y=0$,
and the balanced relations give both composites equal to the identity. This is an isomorphism of
sheaves by sheafifying these maps [def-pur-sheaf-tensor-product]. In particular
$\overline{\mathcal E}$ is flat, since its tensor functor on $k_\ell$-sheaves is the restriction
of the exact tensor functor of $\mathcal E$. Derived direct images with either coefficient ring
agree on underlying abelian complexes by [lem-weil-pbc-exchange-forget-coefficients](2). More
explicitly, for either $u=g$ or $u=h$ and any $k_\ell$-module sheaf $H$, choose a bounded-below
injective $k_\ell$-resolution $H\to J^\bullet$. Each term is acyclic for the $R$-module direct
image: the coefficient-forgetting comparison first with $k_\ell$ and then with $R$ identifies its
higher direct images with the same abelian higher direct images, which vanish. Hence
$u_*J^\bullet$ computes the derived direct image with both coefficients by
[src-right-derived-functor-plus-acyclic-unit]. Its hypotheses hold by
[lem-weil-pbc-module-sheaves-enough-injectives] and [lem-weil-pbc-module-direct-image-left-exact].
This gives the natural $R$-linear identification of $Ru_*$ with restriction of the
$k_\ell$-coefficient $Ru_*$, not merely an abstract isomorphism of underlying abelian objects. For
the left side use $u=g$, $H=\mathcal F$ and apply the balanced tensor identity termwise to
$(f')^{-1}g_*J^\bullet$. For the right side first use that identity on sheaves to identify
$h^{-1}p^{-1}\mathcal E\otimes_R e^{-1}\mathcal F$ with $H=h^{-1}p^{-1}\overline{\mathcal
E}\otimes_{k_\ell}e^{-1}\mathcal F$, and only then take a $k_\ell$-injective resolution of this
$H$ for $u=h$. Thus no assertion that tensoring an $h_*$-acyclic resolution preserves
$h_*$-acyclicity is needed. The flat factors compute the derived tensors, and exact tensor
commutes with cohomology [lem-weil-pbc-exact-functor-complex-cohomology]. Inverse image is exact
[prop-weil-pbc-inverse-image-modules-exact], so the same balanced maps identify the pulled-back
factors. The comparison itself is unchanged: its adjoint sends the pulled-back tensor $\bar
x\otimes s$ to $\bar x\otimes\varepsilon_g(s)$ with either coefficient ring, by the stated counit
formula. We have reduced to sheaves of $k_\ell$-vector spaces. Here $\ell$ is invertible in $K$,
because it divides $n$.

5. We first supply the arbitrary-$K$-scheme version of the untensored base change needed below;
the existing [lem-kun-0f1i] states only its finite-type case. Let $Z$ be any $K$-scheme, retain
$g:T\to S'$ qcqs, and let $\mathcal G$ be a $k_\ell$-module sheaf on $T$, with $\ell$ invertible
in $K$. We first work with its underlying abelian sheaf. The assertion for $Z$ is local on $Z$:
for an open $U\subseteq Z$ its pullback $U\times_K S'$ is open, and
[lem-weil-pbc-derived-open-restriction], applied with the finite ring $k_\ell$, identifies
restriction of the module right direct image with that of the restricted square. Forgetting
coefficients via [lem-weil-pbc-exchange-forget-coefficients](1)–(3) gives the same restriction
identification and canonical comparison for the underlying abelian sheaf. The left side simply
restricts by inverse image. The comparison restricts to the same counit-defined comparison. We may
take $Z=\operatorname{Spec}A$. The finitely generated $K$-subalgebras $A_i\subseteq A$ form a
small directed poset (the algebra generated by the union bounds any two); $A=\varinjlim_i A_i$,
since every element and every finite ring equation occurs in such an algebra. Thus
$Z=\varprojlim_i\operatorname{Spec}A_i$ by [lem-weil-pbc-spec-small-colimit-limit]. The squares
with upper left $\operatorname{Spec}A_i\times_KS'$, upper right $\operatorname{Spec}A_i\times_KT$,
and lower row $T\xrightarrow g S'$ have this square as limit by [lem-kun-fibre-product-limits].
All transitions are affine (between affine $K$-schemes and then by base change
[lem-weil-pbc-affine-morphism-permanence]); the lower transitions are identities. The sheaf system
on $T$ is constant with value $\mathcal G$ and hence has colimit $\mathcal G$. For every $q\ge0$,
[lem-kun-0f1i] gives the stage degree-$q$ comparison isomorphisms, and [lem-kun-0ezt] gives their
limit comparison isomorphism. In the application here $\mathcal G$ is the underlying sheaf of
$\mathcal F$, so its required torsion condition is [lem-kun-zn-sheaf-invertible-orders] with
$n=\ell$. The module comparison follows from [lem-weil-pbc-exchange-forget-coefficients].
Therefore the untensored comparison for $\mathcal F$ is an isomorphism for every $Z$ over $K$,
without any finite-type assumption on $Z,S'$ or $T$.

6. For $k_\ell$-sheaves $M$ on $X$ define $$A^q(M)=p^{-1}M\otimes_{k_\ell}(f')^{-1}R^qg_*\mathcal
F,\qquad B^q(M)=R^qh_*(h^{-1}p^{-1}M\otimes_{k_\ell}e^{-1}\mathcal F).$$ Every $k_\ell$-module
sheaf is flat: on geometric stalks tensor is ordinary vector-space tensor
[lem-pod-etale-stalk-tensor-scalar], which preserves short exact sequences; stalks are exact
[prop-weil-pbc-geometric-stalks-exact] and detect isomorphisms
[lemma-weil-pbc-geometric-stalk-conservative]. Exactness and conservativity on module sheaves
follow by forgetting coefficients [lem-weil-pbc-module-sheaves-colimits-forgetful](1). Hence exact
tensor and inverse image commute with cohomology [lem-weil-pbc-exact-functor-complex-cohomology],
and the degree-$q$ map of $\alpha_{M,\mathcal F}$ is a natural map $a^q_M:A^q(M)\to B^q(M)$. Each
$A^q$ is an exact functor of $M$. The $B^q$ have the long exact sequences obtained by applying
$Rh_*$ to the short exact sequence after the exact functor $M\mapsto h^{-1}p^{-1}M\otimes
e^{-1}\mathcal F$; the required distinguished triangle is [lem-weil-pbc-complex-ses-triangle], and
$Rh_*$ is triangulated as in Step 1. All the $a^q$ commute with the maps in these sequences by the
functorial counit construction. Negative degrees on both sides vanish.

7. As in Step 5, restriction along the open sets of $X$ commutes with this comparison by
[lem-weil-pbc-derived-open-restriction], so assume $X$ affine. It is qcqs by
[lem-weil-pbc-affine-scheme-qcqs]. Use [lem-weil-pbc-module-sheaf-colimit-constructible], with the
finite ring $k_\ell$, to write any $M$ as a small filtered colimit of constructible
$k_\ell$-sheaves $M_i$. Inverse images preserve this colimit because they are left adjoints
[prop-weil-pbc-inverse-image-modules-exact; lem-weil-pbc-left-adjoint-preserves-colimits]. Tensor
preserves it by [lem-weil-pbc-independent-sheaf-tensor-colimits]. Finally $h$ is qcqs as a base
change of $g$ [lem-weil-pbc-qcqs-morphism-permanence](3), so its higher direct images preserve
these torsion filtered colimits by [lemma-weil-pbc-direct-image-filtered-colimit]. Forgetting
module coefficients commutes with colimits [lem-weil-pbc-module-sheaves-colimits-forgetful] and
with higher direct images [lem-weil-pbc-exchange-forget-coefficients]. Consequently
$a^q_M=\varinjlim_i a^q_{M_i}$. These filtered colimits are exact by
[lem-pc-module-filtered-colimits-tensor]. It is enough to prove injectivity, or surjectivity, of
$a^q$ on constructible $M$ to obtain it on all $M$. This uses the qcqs constructible-generation
node, not the narrower finite-type node lem-kun-03sa.

8. For a constructible $M$ on affine $X$,
[lem-weil-pbc-constructible-module-finite-pushforward-embedding] gives a monomorphism
$M\hookrightarrow P=\bigoplus_i\pi_{i,*}\underline{V_i}$ with $\pi_i:X_i\to X$ finite and locally
of finite presentation and $V_i$ finite $k_\ell$-modules. Choosing a finite basis of each $V_i$
identifies $\underline{V_i}$ with a finite direct sum of $\underline{k_\ell}$, so it suffices to
handle $M=\pi_*\underline{k_\ell}$. Form $X'_i=X_i\times_X X'$ and $Y_i=X'_i\times_{X'}Y$, with
projections $\pi':X'_i\to X'$, $\rho:Y_i\to Y$, $h_i:Y_i\to X'_i$ and $e_i=e\rho:Y_i\to T$. These
are the diagram in the last paragraph of 0F1J. Base changes $\pi'$ and $\rho$ of $\pi$ are finite
by [lem-weil-pbc-finite-morphism-permanence](a). They are therefore proper by
[lem-weil-pbc-finite-proper], and their direct images are exact by
[lemma-weil-pbc-finite-direct-image-exact] (also for $k_\ell$-modules by
[lem-weil-pbc-exchange-forget-coefficients]). Finite exchange [lemma-weil-pbc-finite-exchange],
the projection formula [lem-kun-0f0g] for these finite proper morphisms and the torsion ring
$k_\ell$, and the derived composition isomorphism $R(u\circ v)_*\cong Ru_*\circ Rv_*$
[def-weil-pbc-derived-direct-image-composition] give canonical identifications
$$A(\pi_*\underline{k_\ell},\mathcal F)\cong\pi'_*((\pi')^{-1}(f')^{-1}Rg_*\mathcal F),$$
$$B(\pi_*\underline{k_\ell},\mathcal F)\cong\pi'_*Rh_{i,*}e_i^{-1}\mathcal F.$$ Indeed, finite
exchange first replaces $p^{-1}\pi_*\underline{k_\ell}$ by $\pi'_*\underline{k_\ell}$ and
$h^{-1}p^{-1}\pi_*\underline{k_\ell}$ by $\rho_*\underline{k_\ell}$. The two projection formulas
replace tensor with these sheaves by $\pi'_*((\pi')^{-1}-)$ and $\rho_*\rho^{-1}(-)$; then
$h\rho=\pi'h_i$ gives the second identity by composition. Abelian derived composition and
finite-exactness transfer to module coefficients through
[lem-weil-pbc-exchange-forget-coefficients]. Under these identities the comparison is $\pi'_*$ of
the untensored exchange for $X_i$ and $g$, which is invertible by Step 5. To check the map rather
than just its endpoints, use the commuting projection/exchange square
[lem-kun-proj-formula-natural] for the finite maps and paste adjunction mates
[lem-weil-pbc-mate-pasting](2): the composite counit is $\varepsilon_{h_i}\circ
h_i^{-1}\varepsilon_{\pi'}$, and the resulting adjunct is exactly $e_i^{-1}g^{-1}Rg_*\mathcal
F\xrightarrow{e_i^{-1}\varepsilon_g}e_i^{-1}\mathcal F$, with the tensor unit on $X_i$. This is
the defining adjunct of the untensored exchange. Thus $a^q_P$ is an isomorphism for all $q$, by
finite additivity. No claim that $X_i$ is finite type over $K$ is needed, and no claim that $P$ or
its quotient is constructible is used.

9. Here are the omitted dimension-shifting details. First fix any $q\ge0$. For every constructible
$M$, choose $M\hookrightarrow P$ as in Step 8. If a local section of $A^q(M)$ maps to zero under
$a^q_M$, its image in $A^q(P)$ maps to zero under the isomorphism $a^q_P$, and hence is zero.
Exactness of $A^q$ makes $A^q(M)\to A^q(P)$ monic, so the original section is zero. This proves
injectivity for constructible $M$, and Step 7 proves it for every sheaf $M$, in every degree. Now
prove surjectivity for all $M$ by induction on $q$. It suffices at each degree to handle
constructible $M$, by Step 7. Write $0\to M\to P\to C\to0$; $C$ may be any sheaf. For $q=0$,
$B^0(M)\to B^0(P)$ is monic by left exactness. For $q>0$, induction gives that $a^{q-1}_C$ is
surjective, and the map $A^{q-1}(P)\to A^{q-1}(C)$ is surjective by exactness of $A^{q-1}$.
Together with the isomorphism $a^{q-1}_P$, these imply that $B^{q-1}(P)\to B^{q-1}(C)$ is
surjective. The long exact sequence from Step 6 then makes $B^q(M)\to B^q(P)$ monic as well. Given
a local section $b\in B^q(M)$, its image in $B^q(P)$ comes from $a\in A^q(P)$ by Step 8. The image
of $a$ in $A^q(C)$ has zero image under $a^q_C$, since the composite $B^q(M)\to B^q(P)\to B^q(C)$
is zero. Injectivity already proved for arbitrary $C$ forces that image to vanish. Exactness
gives, locally, a lift $a_M\in A^q(M)$ of $a$. The images of $a^q_M(a_M)$ and $b$ in $B^q(P)$
coincide; monicity of $B^q(M)\to B^q(P)$ makes them equal. This proves surjectivity. All lifting
statements here are local on an etale test object, as appropriate for exactness of sheaves.
Therefore every $a^q_M$ is an isomorphism. This is a diagram chase using the exact sequences
established in Steps 6–8; no extra effacement theorem or constructibility of $C$ is assumed.

10. Step 9 proves the comparison for two sheaves over $k_\ell$ in all nonnegative cohomological
degrees, and the negative degrees vanish by Step 6. A derived morphism inducing cohomology
isomorphisms is invertible: after forgetting coefficients use
[lem-weil-pbc-derived-stalk-conservative] (the induced stalk maps are isomorphisms), and reflect
isomorphisms back by the conservative coefficient-forgetting functor of
[lem-kun-unbounded-abelian-exchange-comparison]. The prime-torsion induction in Step 4 now proves
the assertion for a flat $R$-sheaf $\mathcal E$ and an arbitrary $R$-sheaf $\mathcal F$; Step 3
gives every bounded-below $F$; Step 2 gives the original $E$ of lower tor amplitude. At every
reduction it was the natural counit-defined comparison that was compared, so the resulting
isomorphism is the canonical map of the statement. -/
theorem isIso_punctualTensorBaseChangeMap
    (K : Type u) [Field K] (n : ℕ) (hn : 1 ≤ n) (hnK : IsUnit (n : K))
    {X X' Y S' T : Scheme.{u}}
    (aX : X ⟶ Spec (CommRingCat.of K)) (aS : S' ⟶ Spec (CommRingCat.of K))
    (p : X' ⟶ X) (h : Y ⟶ X') (e : Y ⟶ T) (f' : X' ⟶ S') (g : T ⟶ S')
    (left : IsPullback p f' aX aS) (right : IsPullback e h g f')
    [QuasiCompact g] [QuasiSeparated g]
    (E : _root_.DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))))
    (F : _root_.DerivedCategory.Plus
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} (ZMod n)))))
    (a : ℤ) (hE : DerivedCategory.hasTorAmplitudeGE (ULift.{u + 1} (ZMod n)) X a
      (_root_.DerivedCategory.Plus.ι.obj E)) :
    IsIso (punctualTensorBaseChangeMap (ULift.{u + 1} (ZMod n)) p h e f' g right.toCommSq
      (_root_.DerivedCategory.Plus.ι.obj E) (_root_.DerivedCategory.Plus.ι.obj F)) :=
  sorry

end AlgebraicGeometry.Etale
