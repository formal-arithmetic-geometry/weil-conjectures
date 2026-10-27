/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q17
-/
module

public import Sheaf.AlgebraicGeometry.PhSchemeSite
public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparison
public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparisonIdentity
public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparisonComposition
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Sites.Limits
import Sheaf.AlgebraicGeometry.PhAffineStandardSieveBasis
import WeilConjectures.AlgebraicGeometry.EtaleGeometricPointSectionsStalkNatural
import WeilConjectures.AlgebraicGeometry.EtaleSetInverseImageRestriction

/-!
# Sections of an étale set sheaf form a big ph sheaf

Source: Stacks Project, Étale Cohomology, Tag 0DDW, sheaf assertion;
Topologies, Tag 0DBQ (blueprint: lem-sfb-etale-set-sections-ph-sheaf).

The base change of the final étale object `T/T` along `b : W ⟶ T` is a final
object of `W.Etale`: its structure map is the isomorphism `T ×[T] W ⟶ W`.
Evaluating `b⁻¹F` there therefore computes exactly `Γ(W_et, b⁻¹F)`.
This choice lets the existing canonical section-comparison maps give the
restriction maps without any new inverse-image or composition construction.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- The presheaf `W ↦ Γ(W_et, b⁻¹F)` on all schemes over `T`, with restrictions
obtained by the inverse-image adjunction unit and its uniquely unit-compatible
composition comparison. Global sections are evaluated at the base change of the
terminal étale object of `T`; this is terminal over `W`, canonically isomorphic to
`W/W`. Its identity and composition laws are the existing section-comparison laws.

Source: Stacks Project, Étale Cohomology, Tag 0DDW, displayed rule and preceding
setup in Tag 09XN (blueprint: lem-sfb-etale-set-sections-ph-sheaf). -/
noncomputable def etaleSetSectionsPresheaf (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (Type (u + 1))) :
    (Over T)ᵒᵖ ⥤ Type (u + 1) where
  obj W := ((etaleSetPullback W.unop.hom).obj F).obj.obj
    (op ((MorphismProperty.Over.pullback @Etale ⊤ W.unop.hom).obj (Etale.mk (𝟙 T))))
  map {W W'} c := etaleSetSectionComparison c.unop.left W.unop.hom W'.unop.hom
    c.unop.w F (Etale.mk (𝟙 T))
  map_id W := etaleSetSectionComparisonIdentity W.unop.hom F (Etale.mk (𝟙 T))
  map_comp {W W' W''} c d := (etaleSetSectionComparisonComposition c.unop.left
    d.unop.left W.unop.hom W'.unop.hom W''.unop.hom c.unop.w d.unop.w F
    (Etale.mk (𝟙 T))).symm

/-- For an arbitrary small étale sheaf of sets `F`, its inverse-image sections
presheaf is a sheaf for the big ph topology. No algebraic structure, torsion,
constructibility, Noetherianity, or finite-presentation hypothesis is imposed.

Source: Stacks Project, Étale Cohomology, Tag 0DDW, sheaf assertion, and
Topologies, Tag 0DBQ (blueprint: lem-sfb-etale-set-sections-ph-sheaf).

Proof plan (the ten reviewed DAG steps):

1. The unit-compatible composition isomorphisms of
[lem-weil-pbc-sets-etale-inverse-image-composition-units] give $(cd)^*s=d^*(c^*s)$ after the
specified identifications; the identity unit acts as the identity by the adjunction identity.
Hence the displayed rule defines a presheaf. For $b:W\to T$ put $G=b^{-1}F$. An open immersion
$j:O\hookrightarrow W$ is etale by [lem-weil-pbc-open-immersion-etale]. By
[lem-weil-pbc-sets-etale-inverse-image-restriction], $j^{-1}G$ is the restriction of $G$ and its
unit pulls a section back by ordinary restriction. Combining this with the composition-unit
formula identifies $H_F(O)$ and all its open restriction maps with $G(O)$. The sheaf axiom
[def-weil-pbc-etale-sheaf-of-sets] for $G$ on the small etale site therefore proves Zariski
gluing for $H_F$, including the empty covering of the empty scheme.

2. Fix any proper surjection $p:V\to W$ over $T$ and keep $G=b^{-1}F$. Put $Q=V\times_WV$, with
projections $r_i$ and $q=pr_i$, using [def-pc-fibre-product]. Let $A=p_*p^{-1}G$ and
$B=q_*q^{-1}G$. For $i=1,2$ let $\alpha_i:A\to B$ be $p_*$ of the unit for $r_i$, followed by
the composition comparisons; direct-image evaluation is $(p_*K)(U)=K(U\times_WV)$ by
[lem-weil-pbc-sets-etale-inverse-image-composition-units]. The unit $\eta:G\to A$ equalizes
them, because both composites are the unit for $q$. By
[lem-weil-pbc-site-sheaf-sets-limits-sectionwise] the sheaf equalizer $E$ exists and is computed
as $E(U)=\{z\in A(U):\alpha_1z=\alpha_2z\}$. Write $\theta:G\to E$ for the unit factorization.
We will prove $\theta$ is an isomorphism.

3. Each $r_i$ is a base change of $p$, hence proper by [lem-weil-pbc-proper-base-change];
$q=pr_1$ is proper by [lem-weil-pbc-proper-composition]. For a geometric point
$s:P=\operatorname{Spec}\Omega\to W$, with $\Omega$ algebraically closed, put $V_s=V\times_WP$,
$a:V_s\to P$, and $Q_s=Q\times_WP$. Fibre-product universality [def-pc-fibre-product] identifies
$Q_s=V_s\times_PV_s$, its projections $\rho_i$, and its structure map $d=a\rho_i$. The
base-change lemmas make $a$ proper and surjective, so $V_s$ is nonempty and, by
[def-weil-proper-morphism], of finite type over $\Omega$. By
[lem-sc-lft-over-field-jacobson-space] it has a closed point $v$. By
[lem-weil-pbc-closed-point-residue-field-base], $\operatorname{Spec}\kappa(v)\to P$ is an
isomorphism. Its inverse followed by the point map gives $e:P\to V_s$ with $ae=1_P$. This
section exists only on the geometric fibre; we do not claim a section of $p$.

4. Put $L=s^{-1}G$. Apply [lem-sfb-scheme-proper-set-sheaf-base-change] to $p$ with sheaf
$p^{-1}G$ and to $q$ with sheaf $q^{-1}G$, along $s$. The morphisms are proper by step 3 and all
objects are schemes, so both applications have exactly their required hypotheses. Using
inverse-image composition [lem-weil-pbc-sets-etale-inverse-image-composition-units] and taking
sections over $P$ gives $\Gamma(P,s^{-1}A)\cong\Gamma(V_s,a^{-1}L)$ and
$\Gamma(P,s^{-1}B)\cong\Gamma(Q_s,d^{-1}L)$. By
[lem-weil-pbc-geometric-point-sections-stalk-natural] these identify $A_s$ and $B_s$ with the
indicated fibre sections, and $G_s$ with $\Gamma(P,L)$. All these are bijections of sets, with
no group structure or torsion requirement.

5. We check the arrows in these identifications. For $f:Z\to W$ and its fibre square with $s$,
write $j:Z_s\to Z$ and $\beta:s^{-1}f_*K\to f_{s,*}j^{-1}K$ for the counit mate of
[lem-sfb-scheme-proper-set-sheaf-base-change]. Transposing its defining counit composite and
cancelling $\epsilon_f f^{-1}\circ f^{-1}\eta_f=1$ gives
$s_*\beta\circ\eta_{s,f_*K}=f_*\eta_{j,K}$ under $s_*f_{s,*}=f_*j_*$. Thus on a germ represented
by $z\in K(Z\times_WU)$ at a pointed neighbourhood $(U,u)$, the fibre-section map pulls $z$ back
along $(\operatorname{pr}_Z,u\operatorname{pr}_P):Z_s\to Z\times_WU$. The representative formula
of [lem-weil-pbc-geometric-point-sections-stalk-natural] gives exactly this germ. Applying this
to $p,q$, a representative of $\alpha_i z$ is the pullback of $z$ along $Q\times_WU\to
V\times_WU$. Restricting it to $Q_s$ is the same as first restricting $z$ to $V_s$ then pulling
back along $\rho_i$: the two maps to $V\times_WU$ have the same projections
[def-pc-fibre-product]. For a germ of $G$ both composites pull its representative back to $V_s$.
The unit-composition formula [lem-weil-pbc-sets-etale-inverse-image-composition-units] therefore
identifies $\eta_s$ with $a^*$ and $(\alpha_i)_s$ with $\rho_i^*$.

6. If $z\in\Gamma(V_s,a^{-1}L)$ equalizes $\rho_1^*,\rho_2^*$, pull that equality back along
$h=(1_{V_s},ea):V_s\to V_s\times_PV_s$. By [def-pc-fibre-product] its composites are $\rho_1h=1$
and $\rho_2h=ea$. Hence $z=a^*(e^*z)$ by the unit-composition formula
[lem-weil-pbc-sets-etale-inverse-image-composition-units]. Conversely $a^*t$ equalizes because
$a\rho_1=a\rho_2$, and $e^*a^*t=t$ because $ae=1$. This proves the fibre equalizer bijection
with inverse $z\mapsto e^*z$. It works for every sheaf $L$, including when its section set is
empty; connectedness or reducedness of $V_s$ is unnecessary.

7. By [lem-weil-pbc-sets-etale-stalk-finite-limits], $E_s$ is the equalizer of $(\alpha_i)_s$.
Steps 4--6 show that $\theta_s:G_s\to E_s$ is bijective. Choose a geometric point above each
point of $W$; [lem-weil-pbc-sets-etale-iso-on-geometric-stalks] makes $\theta$ an isomorphism.
For empty $W$ the same criterion uses the empty family, so no geometric fibre has to be chosen.
Evaluating the equalizer at $W$ by [lem-weil-pbc-site-sheaf-sets-limits-sectionwise] now proves
that $\Gamma(W,G)\to\Gamma(V,p^{-1}G)\rightrightarrows\Gamma(Q,q^{-1}G)$ is an equalizer with
the specified projection pullbacks. By the composition formula
[lem-weil-pbc-sets-etale-inverse-image-composition-units], these are exactly
$H_F(W),H_F(V),H_F(Q)$ and their restriction maps. Thus $H_F$ has unique descent for every
singleton proper surjection over $T$.

8. We finish the topology argument explicitly, rather than assuming descent for the generators
suffices without base changes. Let $\{W_i\to W\}$ be any ph covering family. Its generated sieve
pulls back to a covering sieve on every affine open $A\subset W$ by [def-trf-ph-scheme-site,
def-weil-pbc-topos]. By [lem-trf-ph-affine-standard-sieve-basis], it contains a standard family
$V_k\to V\xrightarrow{p}A$, where $p$ is proper surjective and the finitely many $V_k$ form an
affine open cover of $V$, each composite factoring through some $W_i$. If two sections of
$H_F(W)$ agree on all $W_i$, they agree on $V_k$, hence on $V$ by step 1, and on $A$ by the
injectivity in step 7. An affine open cover exists by [lem-pc-fppf-affine-open-cover], so step 1
makes them equal on $W$. This proves separatedness for every ph covering family, including every
base change of the given family.

9. First suppose $W=A$ affine and let $s_i\in H_F(W_i)$ be a matching family. Choose the
standard refinement from step 8, with a chosen factorization for each $V_k$. Pull back the
corresponding $s_i$ to $V_k$. They agree on $V_k\cap V_l$, since both maps to the original
covering members give a map to their overlap by [def-pc-fibre-product]. Step 1 glues them to
$z\in H_F(V)$. The two pullbacks of $z$ to $V\times_AV$ agree: on the Zariski covering by
$V_k\times_AV_l$ they are restrictions of the two original matching sections. Step 1 detects
their equality there. Step 7 therefore gives a unique $t_A\in H_F(A)$ pulling back to $z$. For
each $i$, its pullback and $s_i$ agree on every $V_k\times_AW_i$, by the original matching
condition and the defining property of $z$. This is a ph covering of $W_i$: the standard
refinement is covering by [lem-trf-ph-affine-standard-sieve-basis] and covering sieves are
stable under pullback [def-weil-pbc-topos]. Step 8 then gives equality on $W_i$. Thus $t_A$
amalgamates the whole original family, not just the refinement.

10. For general $W$, choose an affine open covering $\{A_j\}$ by
[lem-pc-fppf-affine-open-cover]. Apply step 9 to the ph covering $\{W_i\times_WA_j\to A_j\}$ and
the restricted matching family, obtaining $t_j$. On $A_j\cap A_l$, their restrictions agree
after the covering pulled back from $\{W_i\to W\}$, as both restrict to the given $s_i$. Step 8
proves that they agree on the intersection, without requiring that intersection to be affine.
Step 1 glues the $t_j$ to $t\in H_F(W)$. On each $W_i$, $t$ and $s_i$ agree on its open cover
$\{W_i\times_WA_j\}$, hence agree by step 1. Uniqueness is step 8. Every refinement and fibre
product used stays in [def-weil-size-convention]; the basis node explicitly includes empty
affine targets and empty covers. This proves the ph sheaf axiom for the original presheaf and
its specified restriction maps, for arbitrary $F$. Finally apply the family assertion to the
small family of all arrows of any covering sieve. Its compatibility is exactly a matching family
on that sieve, so existence and uniqueness are the sieve sheaf axiom of [def-weil-pbc-topos].
-/
theorem isSheaf_etaleSetSectionsPresheaf (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology (Type (u + 1))) :
    Presheaf.IsSheaf (phTopology T) (etaleSetSectionsPresheaf T F) := by
  sorry

end AlgebraicGeometry.Scheme
