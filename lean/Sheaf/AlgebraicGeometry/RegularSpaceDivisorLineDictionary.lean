module

public import Sheaf.AlgebraicGeometry.SpaceDivisorPullback
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceSchemeRestriction
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible

import Sheaf.SixFunctors.TraceFormula.SchemeEtaleInvertibleComparison
import Sheaf.AlgebraicGeometry.SmallEnlargedEtaleModules
import Sheaf.AlgebraicGeometry.AlgebraicSpaceInvertibleDescent
import Sheaf.RingTheory.RegularLocalUFDBoundaryFactorization

/-! # Divisor and rational-line dictionary on regular algebraic spaces

Source: Stacks Project, Spaces Divisors, Tags 0DMM, 0EN6, 0EN7, 0EN9, 0EPQ;
Divisors, Tags 0AGA and 0BE8 (blueprint: lem-sfb-regular-space-divisor-line-dictionary).

The theorem below states the complete Cartier/Weil and rational-section dictionary,
including normalized local equations, dense-open uniqueness, restriction, étale pullback,
and flat pullback. All constructions are the canonical definitions in the preceding
modules; the proof is intentionally postponed.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

/-- The full divisor-line dictionary on a regular Noetherian separated algebraic space.
Source: Stacks, Spaces Divisors, Tags 0DMM, 0EN6, 0EN7, 0EN9 and 0EPQ;
Divisors, Tags 0AGA and 0BE8 (blueprint: lem-sfb-regular-space-divisor-line-dictionary).

Proof:
1. Apply the meromorphic generic-chart model to $X$ and $L$. Each $L_\eta$ is a one-dimensional
vector space over $k(\eta)$; choose a basis $s_\eta$. The tuple $(s_\eta)_\eta$ is a global section
of $\mathcal K_X(L)$ and generates it over $\mathcal K_X$, since componentwise multiplication by a
nonzero basis coordinate is invertible. This gives the asserted nonzero rational section, also when
$X$ is disconnected; for the empty space the tuple is empty. Throughout, use connected affine etale
charts, whose rings are Noetherian normal domains, and interpret line modules on scheme charts by
the ordinary-to-etale equivalence. Uses: lem-sfb-space-meromorphic-generic-chart-model, lem-trf-
scheme-etale-invertible-comparison.
2. A Cartier section is represented on an etale covering by invertible meromorphic functions $f_i$,
with $f_i/f_j$ a regular unit on overlaps. On a connected normal affine chart, the principal-divisor
kernel lemma gives a finite cycle of normalized codimension-one orders; it is additive on
multiplication and vanishes on units. The cycle-descent lemma identifies these cycles under further
etale restriction and descends them to a unique Weil divisor on $X$. Local finiteness is finite
support here: choose a finite covering of the quasi-compact $X$ by affine charts with local
equations; the finite union of their finite order supports has finite image. If two Cartier sections
have the same Weil divisor, their ratio on any connected affine refinement has zero principal
divisor. The kernel lemma says this ratio is a regular unit. The local classes in $\mathcal
K_X^\times/\mathcal O_X^\times$ therefore agree; its sheaf axiom gives equality globally. This
proves injectivity and also makes the order convention unambiguous. Uses: lem-sfb-space-meromorphic-
generic-chart-model, lem-trf-normal-domain-principal-divisor-kernel, lem-sfb-space-codimension-one-
cycle-descent.
3. Conversely, pull a Weil divisor $E$ back to a quasi-compact etale scheme atlas $U$ by cycle
descent. Work on a connected affine open $\operatorname{Spec}R$ of $U$: by the model, $R$ is a
Noetherian normal domain, and it is regular. Fix a point $x$ with prime $\mathfrak q$; discard the
finitely many prime divisors of $E$ on $\operatorname{Spec}R$ not containing $x$ (remove their
union), and let $J_a$ be the primes of the remaining ones, with coefficients $n_a\in\mathbf Z$.
Primes of $R_{\mathfrak q}$ inside $J_aR_{\mathfrak q}$ correspond to primes of $R$ inside $J_a$,
and $\dim R_{J_a}=1$, so $J_aR_{\mathfrak q}$ has height one. The regular local ring $R_{\mathfrak
q}$ is a unique factorization domain by the boundary-factorization lemma with $r=0$, so the height-
one criterion gives $J_aR_{\mathfrak q}=(t_a)$, with $t_a\ne0$ a nonzerodivisor of the domain. The
spreading lemma gives $g_a\notin\mathfrak q$ and $c_a\in J_a$ with $J_aR_{g_a}=(c_a)$; let
$g=\prod_ag_a\notin\mathfrak q$. On $\operatorname{Spec}R_g$, localizing at $J_a$ gives
$J_aR_{J_a}=(c_a)$, so $c_a$ is a uniformizer of the discrete valuation ring $R_{J_a}$ of the kernel
lemma and $v_{J_a}(c_a)=1$. A height-one prime $P\ne J_aR_g$ of $R_g$ does not contain $c_a$, since
otherwise $J_aR_g\subseteq P$ with both of height one; so $v_P(c_a)=0$. Hence
$f=\prod_ac_a^{n_a}\in\operatorname{Frac}(R)^\times$ has divisor precisely the specified sum on
$\operatorname{Spec}R_g$. The equations on overlaps have equal Weil divisors, by cycle descent,
hence their ratios are regular units by the kernel lemma, applied on connected normal affine
refinements. Their classes glue in $\mathcal K_X^\times/\mathcal O_X^\times$. Step 2 proves that
this inverse to the order map is independent of every choice. Thus the Cartier and Weil groups are
canonically identified. Uses: lem-sfb-space-meromorphic-generic-chart-model, lem-sfb-space-
codimension-one-cycle-descent, lem-trf-regular-local-ufd-boundary-factorization, lem-trf-ufd-height-
one, lem-sfb-stalk-nonzerodivisor-cartier-spreading, lem-trf-normal-domain-principal-divisor-kernel.
4. For the Cartier equations $f_i$ of $E$, form $M_i=f_i^{-1}\mathcal O_{U_i}\subset\mathcal
K_{U_i}$. Each is a free line with basis $f_i^{-1}$. If $f_i/f_j$ is a unit, these are equal
submodules of the meromorphic sheaf on the overlap; their identification is the identity on rational
elements and satisfies the triple-overlap cocycle. Etale descent of line modules gives $\mathcal
O_X(E)$; its local injections into $\mathcal K_X$ agree, so the sheaf axiom realizes it as the
subsheaf given by these $M_i$. In its meromorphic localization, the element $1$ agrees on all
overlaps and is a generator. Set $s_E=1$. Relative to $f_i^{-1}$ its coefficient is $f_i$, so Step 2
gives $\operatorname{div}(s_E)=E$. These formulas give the explicit construction in the statement,
including negative coefficients. Uses: lem-sfb-space-meromorphic-generic-chart-model, lem-trf-
algebraic-space-invertible-descent.
5. For any rationally trivialized line $(L,s)$, choose local frames $e_i$ on scheme charts and write
$s=g_i e_i$ with $g_i\in\mathcal K^\times$. A change of frame multiplies $g_i$ by a regular unit, so
its orders define $E=\operatorname{div}(s)$ by Steps 2 and 3. The map $g_i^{-1}\mathcal O\to L$,
$a\mapsto a g_i e_i$, is a regular isomorphism: it sends the basis $g_i^{-1}$ to $e_i$. It sends the
rational section $1$ to $s$. On overlaps both maps send every rational scalar $a$ to $as$, so they
agree by the injective meromorphic embedding of a line. Full faithfulness in etale descent glues
them to $\mathcal O_X(E)\simeq L$. A second such isomorphism has the same meromorphic map, since $1$
generates after meromorphic localization; injectivity of $L\to\mathcal K_X(L)$ makes it equal to the
first. Invert this unique isomorphism to obtain the orientation in the statement. Uses: lem-sfb-
space-meromorphic-generic-chart-model, lem-trf-scheme-etale-invertible-comparison, lem-trf-
algebraic-space-invertible-descent.
6. In the same frame $s=g_i e_i$, it extends to a regular generating section exactly when $g_i$ is a
regular unit. By the principal-divisor kernel lemma on connected normal affine refinements, this
holds exactly when all codimension-one orders of $g_i$ vanish. The extension glues uniquely, since
its images in the meromorphic sheaf agree. Therefore $s$ is everywhere generating if and only if
$\operatorname{div}(s)=0$. This tests the given rational section, rather than just the isomorphism
class of its line. Uses: lem-sfb-space-meromorphic-generic-chart-model, lem-trf-normal-domain-
principal-divisor-kernel.
7. Let $a,b:L\to M$ agree on a dense open $W$. Apply the generic-chart model to the line
$L^\vee\otimes M$: in local frames its regular sections are exactly the coefficients of maps $L\to
M$. The coefficient of $a-b$ restricts to zero on $W$, hence is zero by the dense-open injection of
that model. Thus $a=b$. Open restriction and further etale restriction preserve the equations $f_i$,
the submodules $f_i^{-1}\mathcal O$, and the maps $a\mapsto as$ above, by the meromorphic chart
model. Consequently all the identifications commute with these restrictions. On schemes the
ordinary-to-etale equivalence identifies these lines with the usual invertible modules. Uses: lem-
sfb-space-meromorphic-generic-chart-model, lem-trf-scheme-etale-invertible-comparison.
8. For the flat $q:X'\to X$, use the enlarged ringed-etale-site model to compute module pullback as
tensor inverse image. After choosing charts of $X$ and refining their inverse images by affine
charts of $X'$, the calculation is a flat ring map $A\to A'$ of reduced rings. The total-fraction
comparison lemma states that non-zero-divisors of $A$ map to non-zero-divisors of $A'$ and gives the
map $Q(A)\to Q(A')$, $a/t\mapsto q(a)/q(t)$. Only this first assertion of that lemma is used (its
finite intermediate algebra may be taken to be $A$). Hence every local equation $f_i\in Q(A)^\times$
pulls back to $q(f_i)\in Q(A')^\times$; regular-unit ratios remain units. These equations define a
Cartier divisor, hence by Steps 2 and 3 a Weil divisor $q^*E$ on $X'$. No flat cycle pullback with a
relative dimension assumption is used. Uses: lem-sfb-space-meromorphic-generic-chart-model, lem-trf-
flat-birational-normalization-comparison, lem-trf-space-enlarged-etale-ringed-site-model.
9. Locally $q^*(f_i^{-1}\mathcal O)$ is free with basis $1\otimes f_i^{-1}$, and $1\otimes
f_i^{-1}\mapsto q(f_i)^{-1}$ is an isomorphism to $q(f_i)^{-1}\mathcal O_{X'}$. The rational element
$1=f_i f_i^{-1}$ maps to $q(f_i)q(f_i)^{-1}=1$. The transition ratios are the images of the original
ratios, so these local isomorphisms glue. Likewise $s=g_i e_i$ pulls back to $q(g_i)q^*e_i$, which
is a generator over the meromorphic sheaf since $q(g_i)$ is a unit there. Its divisor is the Weil
divisor represented by the Cartier equations $q(g_i)$, exactly $q^*\operatorname{div}(s)$ by Step 8.
This proves the asserted pullback identity and the isomorphism of pairs; its uniqueness follows as
in Step 5 from the injective meromorphic embedding on $X'$. Uses: lem-sfb-space-meromorphic-generic-
chart-model, lem-trf-algebraic-space-invertible-descent, lem-trf-space-enlarged-etale-ringed-site-
model. -/
theorem regularSpaceDivisorLineDictionary
    (X : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
    (hX : IsRegularNoetherianSeparated X) :
    ∃ (c : SpaceCartierDivisor X ≃ SpaceWeilDivisor X)
      (d : ∀ (L : X.Modules), SpaceRationalSection X L → SpaceCartierDivisor X)
      (line : SpaceCartierDivisor X → X.Modules)
      (sec : ∀ D : SpaceCartierDivisor X, SpaceRationalSection X (line D)),
      (∀ D, SpaceCartierDivisor.HasWeilDivisor X D (c D)) ∧
      (∀ L : X.Modules, X.IsLineModule L → Nonempty (SpaceRationalSection X L)) ∧
      (∀ (L : X.Modules) (s : SpaceRationalSection X L),
        X.IsLineModule L → SpaceRationalSection.HasCartierDivisor X s (d L s)) ∧
      (∀ D, X.IsLineModule (line D) ∧
        SpaceCartierDivisor.IsAssociated X D (line D) (sec D) ∧
        d (line D) (sec D) = D) ∧
      (∀ (L : X.Modules) (s : SpaceRationalSection X L), X.IsLineModule L →
        ∃! e : L ≅ line (d L s),
          SpaceRationalSection.Preserves X s (sec (d L s)) e) ∧
      (∀ (L : X.Modules) (s : SpaceRationalSection X L), X.IsLineModule L →
        SpaceRationalSection.IsRegularGenerator X s ↔ c (d L s) = 0) ∧
      (∀ (L M : X.Modules) (f g : L ⟶ M), X.IsLineModule L → X.IsLineModule M →
        ∀ W : Set (Point X.obj.obj), IsOpen W → Dense W →
          (∀ U : X.SmallEtaleModel,
            (∀ y : (divisorBasisChart X U).left,
              schemePointMap (X.smallEtaleInclusion.obj U).obj.hom y ∈ W) →
            f.val.app (op (X.smallEtaleInclusion.obj U)) =
              g.val.app (op (X.smallEtaleInclusion.obj U))) → f = g) ∧
      (∀ L : X.Modules, X.IsLineModule L ↔
        ∀ T : X.EtaleSite, Scheme.Modules.IsInvertible ((schemeRestriction X T).obj L)) ∧
      (∀ (X' : AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))
        (_hX' : IsRegularNoetherianSeparated X') (q : X' ⟶ X) (hq : MapIsFlat q),
        ∃ (c' : SpaceCartierDivisor X' ≃ SpaceWeilDivisor X')
          (d' : ∀ (L : X'.Modules), SpaceRationalSection X' L → SpaceCartierDivisor X')
          (line' : SpaceCartierDivisor X' → X'.Modules)
          (sec' : ∀ D : SpaceCartierDivisor X', SpaceRationalSection X' (line' D))
          (pullD : SpaceCartierDivisor X → SpaceCartierDivisor X')
          (pullS : ∀ (L : X.Modules), SpaceRationalSection X L →
            SpaceRationalSection X' ((moduleTensorPullback q).obj L)),
          (∀ D, SpaceCartierDivisor.HasWeilDivisor X' D (c' D)) ∧
          (∀ (L : X'.Modules) (s : SpaceRationalSection X' L),
            X'.IsLineModule L → SpaceRationalSection.HasCartierDivisor X' s (d' L s)) ∧
          (∀ D, X'.IsLineModule (line' D) ∧
            SpaceCartierDivisor.IsAssociated X' D (line' D) (sec' D)) ∧
          (∀ D, SpaceCartierDivisor.IsFlatPullback q hq D (pullD D)) ∧
          (∀ (L : X.Modules) (s : SpaceRationalSection X L),
            X.IsLineModule L → SpaceRationalSection.IsFlatPullback q hq s (pullS L s)) ∧
          (∀ (L : X.Modules) (s : SpaceRationalSection X L), X.IsLineModule L →
            d' ((moduleTensorPullback q).obj L) (pullS L s) = pullD (d L s)) ∧
          (∀ D, ∃! e : (moduleTensorPullback q).obj (line D) ≅ line' (pullD D),
            SpaceRationalSection.Preserves X' (pullS (line D) (sec D))
              (sec' (pullD D)) e)) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
