/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q34
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleComparisonTorsor
public import Sheaf.AlgebraicGeometry.ClassicalContinuityMap
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Sheaf.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Sheaf.Paper.SliceSiteLocalization
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesUnit
import Sheaf.CategoryTheory.PeSiteSheafGluing
import Sheaf.CategoryTheory.SiteCoveringAxioms
import Sheaf.AlgebraicGeometry.ProEtaleClassicalSheavesImage
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.AlgebraicGeometry.ProEtaleTorsorComparisonAffine
import Sheaf.CategoryTheory.Sites.ConstructibleTorsor

/-! # Gluing the etale models of a torsor

Source: the current blueprint, sec-proetale-coefficients/sk-lem-pe-torsor-comparison,
`sk-lem-pe-torsor-comparison-glue.md`; Stacks Project, Tag 099X
(blueprint: det-pe-torsor-comparison-glue).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProEtale

/-- Every torsor under the inverse image of an etale group sheaf descends to an etale
torsor. The model together with its specified comparison is unique up to unique equivariant
isomorphism commuting with that comparison. The original torsor is classical and is trivial
on an etale covering of the scheme.

Source: current blueprint, `sk-lem-pe-torsor-comparison-glue.md`, proof paragraphs 1--3;
Stacks Project, Tag 099X (blueprint: det-pe-torsor-comparison-glue).

Proof:
1. First fix the restriction identifications used throughout. By
[lem-weil-pbc-etale-site-localization-open], for any etale morphism $W\to X$ (in particular any
open subscheme) the slice $X_{\Et}/W$ is $W_{\Et}$ as a site, not just at the level of abelian
sheaves. Part (1) of [lem-weil-proetale-weakly-etale-localization] identifies $X_{\Proet}/W$ with
$W_{\Proet}$ and their set sheaves. The inclusion in [def-weil-pbc-site-comparison-morphism] views
every etale object as weakly etale, so both site-identification hypotheses hold. Apply
[lem-weil-pbc-slice-site-localization] to the continuous inclusion defining $\nu_X$ in
[def-weil-pbc-site-comparison-morphism]. On the localized sites the inclusion is exactly the
inclusion defining $\nu_W$. Hence there is a natural isomorphism
$r_{W,F}:(\nu_X^*F)|_W\xrightarrow{\sim}\nu_W^*(F|_W)$. Use these canonical identifications on all
overlaps. For composable etale maps $Z\to W\to X$, denote this isomorphism by $r^X_{W,F}$. Under
the sectionwise relocalization identifications, $r^X_{Z,F}=r^W_{Z,F|_W}\circ(r^X_{W,F})|_Z$.
Indeed, the inclusion and forgetful slice functors commute on objects and arrows; the two
comparison maps are adjunction mates of that same commuting composite square, so the adjunction
bijection makes them equal. The isomorphisms preserve finite products since both routes are
finite-limit-preserving inverse images; thus they identify the restricted group actions.
Restricting a torsor gives a torsor: simple transitivity and a local section can be checked on the
same objects and covering families of these slice sites.

2. Choose a set-indexed affine open cover $X=\bigcup_aX_a$ (no quasi-compactness or
quasi-separatedness is required). An open cover is a cover in both sites by [sk-def-pe-site] and
[def-weil-pbc-etale-site]. By step 1 the restriction of $T$ is a $\nu_{X_a}^*(G_0|_{X_a})$-torsor.
Apply [det-pe-torsor-comparison-affine] to each affine scheme $X_a$: obtain a $G_0|_{X_a}$-torsor
$T_{0,a}$, an equivariant isomorphism $\alpha_a:\nu_{X_a}^*T_{0,a}\xrightarrow{\sim}T|_{X_a}$, and
an affine etale surjection $W_a\to X_a$ with $T_{0,a}(W_a)\ne\varnothing$. The same argument
includes $X=\varnothing$, using an empty affine cover.

3. Put $X_{ab}=X_a\cap X_b$. Under step 1 the map $\beta_{ab}=\alpha_b^{-1}\circ\alpha_a$ is an
isomorphism from $\nu_{X_{ab}}^*(T_{0,a}|_{X_{ab}})$ to $\nu_{X_{ab}}^*(T_{0,b}|_{X_{ab}})$. Full
faithfulness in [det-pe-classical-sheaves-unit], applied to the scheme $X_{ab}$, gives a unique
sheaf map $\phi_{ab}$ with $\nu^*\phi_{ab}=\beta_{ab}$. Lift $\beta_{ab}^{-1}$ as well;
faithfulness applied to their two composites proves that $\phi_{ab}$ is invertible. Write
$m_a,m_b$ for the restricted actions. Since $\beta_{ab}$ is equivariant, the pullbacks of
$\phi_{ab}\circ m_a$ and $m_b\circ(\mathrm{id}_{G_0}\times\phi_{ab})$ agree. The finite-product
preservation in [def-weil-pbc-site-comparison-morphism] identifies their domains, and faithfulness
makes the two maps equal. Thus $\phi_{ab}$ is equivariant. On $X_{abc}$, cancellation gives
$\beta_{bc}\beta_{ab}=\alpha_c^{-1}\alpha_a=\beta_{ac}$; faithfulness on this scheme gives
$\phi_{bc}\phi_{ab}=\phi_{ac}$. Likewise $\phi_{aa}=\mathrm{id}$. None of these overlaps is
assumed affine.

4. Apply [lem-pe-site-sheaf-gluing] to the covering $\{X_a\to X\}$ of $X_{\Et}$ and the sheaves
$T_{0,a}$ with the isomorphisms $\phi_{ab}$ from step 3. The small sites and the set-indexed cover
fit the universe convention in that lemma. Since $X$ is final in its small etale site, the slice
over $X$ is the original site. Using the site identifications fixed in step 1, the lemma gives a
sheaf of sets $T_0$ on $X_{\Et}$ and isomorphisms $e_a:T_0|_{X_a}\xrightarrow{\sim}T_{0,a}$
satisfying $\phi_{ab}e_a=e_b$ on every overlap.

5. Define the action on $T_0$ explicitly. For an etale $V\to X$, $g\in G_0(V)$ and $t\in T_0(V)$,
set $V_a=V\times_XX_a$. The sections $e_a^{-1}(g|_{V_a}\cdot e_a(t|_{V_a}))$ agree on
$V_a\times_VV_b$, by the equivariance of $\phi_{ab}$ and $\phi_{ab}e_a=e_b$. The sheaf axiom
[def-weil-pbc-etale-sheaf-of-sets] gives a unique section $g\cdot t$ on $V$. Restriction, the
identity law and associativity hold because they hold on every $V_a$ and the same uniqueness
applies. For $t,t'\in T_0(V)$, the local torsor structures give a unique $g_a\in G_0(V_a)$ sending
$t|_{V_a}$ to $t'|_{V_a}$. Freeness makes these agree on overlaps; the sheaf axiom for $G_0$ glues
them to a unique $g\in G_0(V)$. Finally the chosen sections over the etale surjections $W_a\to
X_a$ of step 2 give local sections of $T_0$ on a jointly surjective etale family over $X$, and on
every test object after base change. These are precisely simple transitivity and local
nonemptiness in [def-constructible-torsor], so $T_0$ is a $G_0$-torsor.

6. The local maps $A_a=\alpha_a\circ\nu_{X_a}^*(e_a)\circ r_{X_a,T_0}$ are equivariant
isomorphisms $(\nu_X^*T_0)|_{X_a}\to T|_{X_a}$. On $X_{ab}$ the equations
$\nu^*\phi_{ab}=\alpha_b^{-1}\alpha_a$ and $\phi_{ab}e_a=e_b$ give $A_b=A_a$; naturality of $r$
from step 1 makes these equations equations between the actual restricted maps. For a pro-etale
object $V\to X$ and $s\in(\nu_X^*T_0)(V)$, apply $A_a$ to $s|_{V\times_XX_a}$ and glue the
resulting compatible sections of $T$ over the open cover of $V$. The sheaf axiom
[def-weil-pbc-sites-and-cohomology] makes this a unique section $\alpha_V(s)$, natural in $V$. For
a morphism $h:V^{\prime}\to V$, both $h^*\alpha_V(s)$ and $\alpha_{V^{\prime}}(h^*s)$ restrict
over $V^{\prime}\times_XX_a$ to $A_a(h^*s)$ by naturality of $A_a$; uniqueness of gluing proves
naturality of $\alpha$. Define $B_V(t)$ for $t\in T(V)$ to be the unique section of
$(\nu_X^*T_0)(V)$ whose restriction over $V\times_XX_a$ is $A_a^{-1}(t|_{V\times_XX_a})$. These
local sections agree because $A_a=A_b$ on overlaps. Restriction of $B_V(t)$ along $h$ and
$B_{V^{\prime}}(h^*t)$ have equal local restrictions, so $B$ is a sheaf map. The restrictions of
$B\alpha$ and $\alpha B$ are $A_a^{-1}A_a$ and $A_aA_a^{-1}$ respectively; the sheaf axiom makes
both composites identities. For local sections $g,s$, the sections $\alpha(gs)$ and $g\alpha(s)$
restrict to $A_a(gs)=gA_a(s)$, so they are equal by uniqueness of gluing. Thus
$\alpha:\nu_X^*T_0\xrightarrow{\sim}T$ is an isomorphism of torsors. This uses the fact in
[sk-def-pe-site] that every open cover is a pro-etale cover, with no finiteness requirement on the
affine cover of $X$.

7. Uniqueness concerns the pair $(T_0,\alpha)$. If $(T'_0,\alpha')$ is another such pair, full
faithfulness in [det-pe-classical-sheaves-unit] on $X$ gives a unique $f:T_0\to T'_0$ with
$\nu_X^*f=(\alpha')^{-1}\alpha$. Its inverse is the unique lift of $\alpha^{-1}\alpha'$, as
verified by faithfulness. The equivariance equation for $f$ follows by applying faithfulness to
the two maps out of $G_0\times T_0$; their pullbacks are equal because $(\alpha')^{-1}\alpha$ is
equivariant and [def-weil-pbc-site-comparison-morphism] preserves finite products. Hence $f$ is
the unique torsor isomorphism satisfying $\alpha'\circ\nu_X^*f=\alpha$. This is the asserted
uniqueness up to unique isomorphism, with the specified comparison to $T$ included.

8. By [det-pe-classical-sheaves-image], the isomorphism $T\cong\nu_X^*T_0$ makes $T$ classical.
The composites $W_a\to X_a\to X$ from step 2 are etale and jointly surjective, so they form an
etale covering by [def-weil-pbc-etale-site]. A chosen section of $T_{0,a}(W_a)$ trivializes $T_0$
there: $g\mapsto g\cdot s_a$ is an isomorphism by simple transitivity, also on every further test
object. Pulling this isomorphism back and using step 1 and $\alpha$ from step 6 trivializes $T$ on
$W_a$. Thus the asserted etale trivializing covering is an actual covering of $X$, not just a
collection of local covers. -/
theorem torsorComparisonGlue (X : Scheme.{u})
    (G₀ : Sheaf X.smallEtaleTopology GrpCat.{u + 1}) (T : ComparisonTorsor G₀) :
    (∃ (T₀ : CategoryTheory.Sheaf.NonabelianTorsor.{u, u + 1, u + 1} X G₀)
      (α : ComparisonTorsor.ModelIso T₀ T),
      ∀ (T₀' : CategoryTheory.Sheaf.NonabelianTorsor.{u, u + 1, u + 1} X G₀)
        (α' : ComparisonTorsor.ModelIso T₀' T),
        ∃! e : T₀.sheaf ≅ T₀'.sheaf,
          etaleTorsorAction T₀ ≫ e.hom =
            (𝟙 (groupSets G₀) ⊗ₘ e.hom) ≫ etaleTorsorAction T₀' ∧
          (comparisonSets X).map e.hom ≫ α'.iso.hom = α.iso.hom) ∧
    IsClassical T.sheaf ∧
    ∃ (I : Type (u + 1)) (U : I → X.Etale),
      (∀ x : X, ∃ (i : I) (y : (U i).left), (U i).hom y = x) ∧
      ∀ i : I, Nonempty (ComparisonTorsor.Trivialization T ((Scheme.toProEt X).obj (U i))) := by
  sorry

end AlgebraicGeometry.ProEtale
