/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpacePurityComparison
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekFiniteness
public import Mathlib.Logic.Equiv.Fin.Basic
public import WeilConjectures.AlgebraicGeometry.AffineSpacePurityCompositionMaps

import WeilConjectures.AlgebraicGeometry.AffineSpacePurityOrderedBlocks
import WeilConjectures.AlgebraicGeometry.AffineSpacePurityCoordinateInvariance
import WeilConjectures.AlgebraicGeometry.IntrinsicCoefficientTwistsUnrestricted
import Mathlib.Algebra.Ring.Parity

/-! # Composition and coordinate interchange for affine-space purity

Source: blueprint sec-smooth-purity/sk-prop-an/prop-pur-affine-space-composition-law.md
(blueprint: prop-pur-affine-space-composition-law).
All transports below are constructed from the specified pullback, tensor and adjunction
comparisons. In particular coordinate interchange uses its actual polynomial map.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
universe u v w
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.AffineSpacePurity
open AffineLinePurity VectorIntegrationSite

/-- Affine-space purity respects block composition and block interchange. The parameters
`d` and `e` represent the positive dimensions d+1 and e+1; hence every allowed dimension
occurs. The first clause is the displayed formula after its canonical source and target
transports. The second is the Koszul sign. The third is equality of the comparison with
its transport by the actual block permutation, so it compares the two coordinate orders.
Source: blueprint sec-smooth-purity/sk-prop-an, proposition and proof Steps 1--4
(blueprint: prop-pur-affine-space-composition-law).

Proof plan from the DAG (the expanded ten-step split):
1. Fix the coefficient and geometric domains. All the projections in the coordinate towers are
separated of finite type between separated finite-type $k$-schemes, with their standard
projective compactifications. Their bases and sources are Noetherian by
[lem-weil-pbc-finite-type-over-noetherian], applied to their finite-type structural maps to
$\operatorname{Spec}k$: a field is Noetherian since its only ideals are $0$ and the unit ideal.
The adjunction on bounded-below etale-origin inputs is [thm-sf-ambient-adjoint-class];
[thm-sf-preservation-class] implies that each intermediate exceptional pullback of $K$ is
bounded constructible of finite Tor amplitude. Thus every occurrence of $\gamma_{p_d,Rp_e^!K}$
is in its declared domain. Twists are locally free rank-one coefficient sheaves by
[prop-weil-twist-preserves]. We may calculate compact-support morphisms on the ordinary etale
site: [lem-sf-proetale-constructible-origin] supplies etale representatives,
[thm-weil-pbc-site-comparison] is fully faithful on $D^+$,
[lem-sf-class-compact-support-comparison] identifies the two compact-support functors, and
[lem-weil-pbc-ringed-topoi-derived-tensor-pullback] applies to $\nu$ as well as to scheme
pullbacks. The exceptional adjunction is transported by the actual Hom bijection of
[thm-sf-ambient-adjoint-class], rather than by an unbounded pro-etale adjoint assumption. The
finite Tor condition is reflected on an etale representative: tensor it with any etale module
sheaf and apply the exact, fully faithful, monoidal $\nu^*$; the resulting tensor has the
required cohomological vanishing, which is reflected on each cohomology sheaf by the faithful
exact inverse image (faithfulness on sheaves follows from full faithfulness on complexes
concentrated in degree zero). This reflection does not require applying bounded-below full
faithfulness to an unbounded tensor complex. These facts identify the transposes and permit
checking their equality on the etale site.
Uses: thm-sf-ambient-adjoint-class, thm-sf-preservation-class, prop-weil-twist-preserves,
lem-sf-proetale-constructible-origin, thm-weil-pbc-site-comparison,
lem-sf-class-compact-support-comparison, lem-weil-pbc-ringed-topoi-derived-tensor-pullback,
lem-weil-pbc-finite-type-over-noetherian.

2. The finite-level twist in the preceding identification is the usual etale torsion twist at
every $n$, including ramified stages. Indeed choose $r\geq1$ with $\ell^rA=0$. From
[def-coefficient-twists-detailed] and clauses (2)--(3) of [lem-pur-twist-sheaf-locally-free],
associativity of ordinary tensor gives $$A(1)=\mathbb Z_\ell(1)\otimes_{\mathbb
Z_\ell}A\cong(\mathbb Z_\ell(1)/\ell^r)\otimes_{\mathbb
Z/\ell^r}A\cong\mu_{\ell^r}\otimes_{\mathbb Z/\ell^r}A.$$ These are rank-one locally free
sheaves; this calculation uses no flatness of $A$ over $\mathbb Z/\ell^r$. Their powers give the
same identification for the positive twists used here. It is compatible with pullback because
roots of unity and all the displayed tensor constructions pull back. Thus the finite torsion
trace construction with annihilator $\ell^r$ is exactly the twist convention in the affine-line
comparison of [def-pur-affine-line-purity-comparison]. No divisibility assumption on $n$ by the
ramification index is introduced.
Uses: def-coefficient-twists-detailed, lem-pur-twist-sheaf-locally-free,
def-pur-affine-line-purity-comparison.

3. Obtain the coherence of $c$ from adjunctions. For $X\xrightarrow f Z\xrightarrow g Y$, use
the composite adjunction [def-weil-pbc-composite-adjunction], whose counit is
$\varepsilon_g\circ Rg_!(\varepsilon_f)$. The mate of
$\alpha_{g,f}:Rg_!Rf_!\xrightarrow{\sim}R(gf)_!$ from [thm-sf-comp-composition] identifies its
right adjoint with $Rf^!Rg^!$ and is $c_{g,f}$. Pasting along the adjunctions in clause (2) of
[lem-weil-pbc-mate-pasting] shows that the two $c$-composites for three arrows are the mates of
the two $\alpha$-composites. Those are equal by the associativity clause of
[thm-sf-comp-composition]; the mate correspondence is a bijection, so the $c$-composites agree.
When one arrow is an identity, the direct-image composition map is the identity by
[thm-sf-comp-composition], and its mate is the identity of the right adjoint by clause (4) of
[lem-weil-pbc-mate-pasting]; hence the corresponding $c$ is the unit identification. Pullback
composition uses [lem-weil-pbc-proetale-derived-pullback-composition]; on constant coefficient
sheaves it is termwise inverse-image composition. Tensor reassociation is that of the tensor
powers defining the twists. This supplies the coherence actually needed when parentheses in the
tower are changed.
Uses: def-weil-pbc-composite-adjunction, thm-sf-comp-composition, lem-weil-pbc-mate-pasting,
lem-weil-pbc-proetale-derived-pullback-composition, def-coefficient-twists-detailed.

4. Prove the displayed composition identity by induction on the length of the first block.
Abbreviate $F_f(M)=Lf^*M(a)[2a]$ for an $a$-coordinate projection. In the ordered tower
[def-pur-affine-space-comparison], appending one line $u$ replaces $\Gamma_{g,K}$ by
$$c_{g,u}^{-1}\circ\gamma_{u,Rg^!K}\circ
F_u(\Gamma_{g,K}),\qquad\Gamma_{\mathrm{id},K}=\mathrm{id}_K.$$ The assertion for a first block
of length one is exactly this recursion. Suppose it holds for a first block $f$ of length $a$,
and append $u$. Substitute $\Gamma_{gf,K}=c_{g,f}^{-1}\gamma_{f,Rg^!K}F_f(\Gamma_{g,K})$ into
the recursion. Naturality of $\gamma_u$ moves $F_u(c_{g,f}^{-1})$ across $\gamma_u$. Here
naturality follows directly by transposing the natural projection-formula composite in
[def-pur-affine-line-purity-comparison], with the natural projection map of
[lem-weil-finite-compact-projection-formula]. The resulting two consecutive $c^{-1}$ maps equal
the reassociated ones by Step 3. The remaining factors $\gamma_u F_u(\gamma_f)$ are precisely
$\gamma_{fu}$ at $Rg^!K$. This proves the induction step. Taking the two block lengths to be
$d,e$ gives exactly the equality in the statement, with source $Lp_{d+e}^*K(d+e)[2d+2e]$ and
target $Rp_{d+e}^!K$. This argument concerns regrouping a fixed ordered list; coordinate
interchange is established separately below.
Uses: def-pur-affine-space-comparison, def-pur-affine-line-purity-comparison,
lem-weil-finite-compact-projection-formula, lem-weil-pbc-mate-pasting, thm-sf-comp-composition.

5. Let $L_Y=\mathbf A^1_Y$, $a:L_Y\to Y$, $T=A_{L_Y}(1)[2]$, $U=Ra_!T$, and $t:U\to A_Y$ the
line integration of [def-pur-affine-line-purity-comparison]. It is compatible with change of
base. To check the specific map, use its defining compactification $a=qj$, and put $\bar
T=A_{\mathbf P^1_Y}(1)[2]$, so $j^*\bar T=T$: the trace $t_q$ and its normalized counit commute
with base change by [lem-asd-ordinary-finite-p1-adjunction], applied with annihilator $\ell^r$
from Step 2. The open-extension comparison is [lem-weil-pbc-etale-shriek-base-change-modules],
and the compact-support exchange and its pasting are [thm-cbc-finite-torsion]. Applying these to
the open-adjunction counit followed by the projective trace, $Rq_*j_!j^*\bar T\to Rq_*\bar
T\xrightarrow{t_q}A_Y$ yields, for a morphism $v:Y'\to Y$ between separated finite-type
$k$-schemes (hence between Noetherian schemes), the equality $$v^*t=t'\circ\operatorname{Ex}_!:\
v^*Ra_!T\longrightarrow A_{Y'}.$$ The module open-extension comparison is applied termwise here;
$T$ is a shifted locally free sheaf and inverse image and extension by zero are exact. The
transport of Step 1 gives the identical equality at the finite pro-etale stage. In particular
every line trace in a product tower is the pullback of this one $t$.
Uses: def-pur-affine-line-purity-comparison, lem-asd-ordinary-finite-p1-adjunction,
lem-weil-pbc-etale-shriek-base-change-modules, thm-cbc-finite-torsion.

6. Write $X_m=L_Y^{\times_Ym}=\mathbf A^m_Y$, $T_m=A_{X_m}(m)[2m]$, $F_mK=p_m^*K\otimes^LT_m$,
and let $\tau_{m,K}:Rp_{m!}F_mK\to K$ be the exceptional transpose of the ordered
$\Gamma_{m,K}$. Put $I_m=\tau_{m,A_Y}$; these are temporary morphisms in this proof. For a tower
$f,g$, the composite-adjunction formula of Step 3 says that the transpose of
$c_{g,f}^{-1}\gamma_{f,Rg^!K}F_f(\Gamma_{g,K})$ is $$\varepsilon_{g,K}\circ
Rg_!(\varepsilon_{f,Rg^!K})\circ Rg_!Rf_!\bigl(\gamma_{f,Rg^!K}\circ F_f(\Gamma_{g,K})\bigr).$$
Combining the middle two factors first gives $Rg_!\tau_{f,Rg^!K}\circ
Rg_!Rf_!F_f(\Gamma_{g,K})$. Naturality of $\tau_f$ changes this to $Rg_!(\Gamma_{g,K})\circ
Rg_!(\tau_{f,F_gK})$. The full transpose is therefore $$\tau_{g,K}\circ Rg_!(\tau_{f,F_gK}).$$
For a line, its definition is $\tau_{1,K}=(1_K\otimes t)\circ\mathrm{PF}^{-1}$. Induction using
this pasted formula and the composition pentagon and naturality of [prop-sf-pf-coherence] now
gives $$\tau_{m,K}=(1_K\otimes
I_m)\circ\mathrm{PF}_{p_m}^{-1}:Rp_{m!}(p_m^*K\otimes^LT_m)\longrightarrow K.$$ Specifically,
two successive inverse projection maps identify the pasted source with $K\otimes Rp_{m!}T_m$ by
that pentagon; naturality moves $1_K$ past the inner trace, leaving the very same pasted map
evaluated at $K=A_Y$, namely $I_m$. This proves the asserted formula and does not assume any
coordinate invariance.
Uses: def-pur-affine-space-comparison, def-pur-affine-line-purity-comparison,
def-weil-pbc-composite-adjunction, lem-weil-pbc-mate-pasting,
lem-weil-finite-compact-projection-formula, prop-sf-pf-coherence.

7. First verify the one-factor object needed for the product-domain induction. Apply
[lem-amb-affine-space-top-trace] only with $S=Y$, $d=1$, and $N=\ell^r$ from Step 2. The ring
$A$ is finite with $NA=0$, $N$ is invertible since $\ell\ne p$, and $Y$ is Noetherian by Step 1.
Its bounded-below input is $A_{\mathbf A^1_Y}(1)[2]$. The source of its isomorphic counit is the
ordinary etale representative of $U$. Step 2 identifies its twist, and
[lem-sf-class-compact-support-comparison] realizes this object on the pro-etale site, giving
$U\cong A_Y$. This is only an object isomorphism; no identification of $I_m$ with a
higher-dimensional top-trace counit is used.
Uses: lem-amb-affine-space-top-trace, lem-sf-class-compact-support-comparison.

8. Apply [lem-pur-affine-space-product-domain] to $B=Y$, $f=a:L_Y\to Y$, $M=T=A_{L_Y}(1)[2]$ and
the object isomorphism $U\cong A_Y$ just obtained. The source coefficient is bounded
constructible of finite Tor amplitude because it is a shifted rank-one locally free Tate sheaf,
by [prop-weil-twist-preserves]. Its relative external powers are $T_m$ by tensor-power
additivity and the even shift identifications. The cited lemma supplies $V_m\cong A_Y$, Tor
amplitude $[0,0]$, and all the typed canonical binary product isomorphisms $\kappa_{m,1}$. In
particular the coefficient $V_m$ has its required finite Tor amplitude before the second
projection formula is invoked; this is the original object induction, now a separate node.
Uses: lem-pur-affine-space-product-domain, prop-weil-twist-preserves.

9. The base-change identities of Step 5 hold over every separated finite-type base used in the
tower; Step 6 identifies $I_m$ with the exceptional transpose specified in
[lem-pur-affine-space-trace-factorization]. Its finite-Tor hypothesis is now Step 8, so that
lemma gives $$I_1=t,\qquad I_{m+1}=(I_m\otimes t)\kappa_{m,1}.$$ Define $\kappa_1=1_U$ and
$\kappa_{m+1}=(\kappa_m\otimes1_U)\kappa_{m,1}$. Induction substitutes $I_m=t^{\otimes
m}\kappa_m$ into the binary equality, giving $I_{m+1}=t^{\otimes(m+1)}\kappa_{m+1}$, with tensor
units suppressed. This substitution uses only functoriality of tensor. Clause (ii) of
[lem-sf-kunneth-coherence] identifies every parenthesization with this same iterated product,
and clause (iv) supplies its projection-formula identification.
Uses: lem-pur-affine-space-trace-factorization, lem-sf-kunneth-coherence.

10. For an adjacent transposition of the $m$ line factors, the symmetry clause of
[lem-sf-kunneth-coherence] identifies the induced map on $Rp_{m!}T_m$ with the corresponding
symmetry of $U^{\otimes m}$. Tensor naturality gives $$(t\otimes
t)\circ\sigma_{U,U}=\sigma_{A_Y,A_Y}\circ(t\otimes t)=t\otimes t,$$ since the symmetry of two
tensor units is the identity. On the source, the tensor sign symmetry of
[def-kun-derived-tensor] is $x\otimes y\mapsto(-1)^{ij}y\otimes x$; for $T=A(1)[2]$ the two
degrees are $-2,-2$, so the sign is $+1$. Locally choose a generator $b$ of the rank-one twist
[prop-weil-twist-preserves]; the unshifted interchange sends $b\otimes b$ to itself, and
consequently is the identity under the twist-additivity identification. For blocks of sizes
$d,e$, interchange sends $b^{\otimes d}\otimes b^{\otimes e}$ to $b^{\otimes e}\otimes
b^{\otimes d}$; both identify with $b^{\otimes(d+e)}$, and the shift sign is
$(-1)^{(-2d)(-2e)}=+1$. It follows from Step 9 that each adjacent coordinate transposition
preserves $I_m$, and hence that every coordinate permutation does. By the projection-formula
compatibility in [lem-sf-kunneth-coherence] and Step 6 it preserves $\tau_{m,K}$ for every $K$,
without moving $K$ past a shifted coordinate factor. Finally the exceptional Hom bijection of
[thm-sf-ambient-adjoint-class] is injective and natural, so equality of these transposes proves
equality of the two transported comparisons. Combined with Step 4 this gives the asserted
composition law and equality for the two block orderings.
Uses: lem-sf-kunneth-coherence, def-kun-derived-tensor, prop-weil-twist-preserves,
thm-sf-ambient-adjoint-class.
-/
theorem affineSpacePurityComposition (P : WeilConjectures.PurityFiniteSetting.{u})
    (Y : Scheme.{u}) (aY : Y ⟶ Spec (.of P.field.k))
    [LocallyOfFiniteType aY] [QuasiCompact aY] [IsSeparated aY]
    (K : Plus (Ring P) Y) (Ke : Etale.DerivedCategoryModule (Ring P) Y)
    (hKe : etaleFiniteTor (Ring P) Y Ke)
    (eK : (comparison (Ring P) Y).obj Ke ≅ K.obj) (d e : ℕ) :
    HEq (transportedComparison P Y aY K Ke hKe eK ((e + 1) + d)
      (eqToIso (blockSchemeEq Y (e + 1) (d + 1)))
      (iteratedAffineLineProj (iteratedAffineLine Y (e + 1)) (d + 1) ≫
        iteratedAffineLineProj Y (e + 1))
      (hg' := blockProjectionCompactification Y (d + 1) (e + 1))
      (blockProjection Y (d + 1) (e + 1)))
      (blockComposite P Y aY K Ke hKe eK d e) ∧
    (-1 : ℤ) ^ ((2 * (d + 1)) * (2 * (e + 1))) = 1 ∧
    HEq (transportedComparison P Y aY K Ke hKe eK ((e + 1) + d)
      (coordinateIso Y ((e + 1) + (d + 1)) (blockPermutation (d + 1) (e + 1)))
      (iteratedAffineLineProj Y ((e + 1) + (d + 1)))
      (hg' := purityProjectionCompactification Y ((e + 1) + (d + 1)))
      (coordinateProjection Y ((e + 1) + (d + 1))
        (blockPermutation (d + 1) (e + 1))))
      (positiveComparison P Y aY K Ke hKe eK ((e + 1) + d)) := by
  refine ⟨affineSpacePurity_orderedBlockEquation P Y aY K Ke hKe eK d e, ?_, ?_⟩
  · exact ((even_two_mul (d + 1)).mul_right (2 * (e + 1))).neg_one_pow
  · exact affineSpacePurity_coordinateEquation P Y aY K Ke hKe eK ((e + 1) + d)
      (blockPermutation (d + 1) (e + 1))

end AlgebraicGeometry.ProEtale.AffineSpacePurity
