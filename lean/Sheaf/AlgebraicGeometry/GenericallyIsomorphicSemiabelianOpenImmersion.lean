module

public import Sheaf.AlgebraicGeometry.SemiabelianGeometricFibres
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Localization.FractionRing

import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Sheaf.AlgebraicGeometry.SemiabelianGeometricPowerIntegrality
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.FunctionField
import Sheaf.AlgebraicGeometry.IntegralBirationalNormalIsomorphism

/-! # A generic isomorphism from a semiabelian model is an open immersion

Source: Brian Conrad, Semistable reduction for abelian varieties, proof of Theorem 4.4,
printed pages 12-16, especially Corollary 3.3 and Lemma 4.9. This is the agent-extracted
version for a given homomorphism into an arbitrary smooth separated target.
(blueprint: lem-sfb-generically-isomorphic-semiabelian-open-immersion)

The source has finite presentation; the target need not be quasi-compact. The generic
map is the actual pullback of the supplied group homomorphism along Spec F -> Spec R.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A given generically isomorphic homomorphism from a semiabelian model over a DVR
is an open immersion into any smooth separated commutative group scheme.

Source: Brian Conrad, Semistable reduction for abelian varieties, proof of Theorem 4.4,
printed pages 12-16; agent-extracted generalization for a given generic isomorphism.
(blueprint: lem-sfb-generically-isomorphic-semiabelian-open-immersion)

Proof plan:

1. Fix a uniformizer $\pi$ and put $k=R/(\pi)$. Finite presentation of $A/T$ implies finite type
   directly from the finite polynomial presentations and quasi-compactness. The graph
   $\gamma=(1_A,a):A\to A\times_T B$ is the pullback of the closed diagonal of $B/T$ along
   $(a\operatorname{pr}_A,\operatorname{pr}_B):A\times_TB\to B\times_TB$. Thus $\gamma$ is a
   closed immersion by [lem-weil-pbc-closed-immersion-base-change], hence proper by
   [lem-weil-pbc-proper-fp-permanence](c), hence of finite type by [def-weil-proper-morphism]. The
   projection $A\times_TB\to B$ is of finite type by
   [lem-sfb-finite-type-composition-base-change](2); its composite with $\gamma$ is $a$, so (1) of
   that node makes $a$ of finite type. Likewise $\Delta_a$ is the pullback of $\Delta_{A/T}$ along
   $A\times_BA\to A\times_TA$. It is closed, so $a$ is separated. None of these assertions
   requires $B/T$ quasi-compact.

2. The generic group $A_F$ is integral. Indeed over an algebraic closure $\overline F$, its
   prescribed semiabelian exact sequence [def-sfb-semiabelian-geometric-fibres] satisfies
   [lem-sfb-semiabelian-geometric-power-integrality] with $n=1$, so $(A_F)_{\overline F}$ is
   integral. For every nonempty affine open $\operatorname{Spec}C\subseteq A_F$, the tensor map
   $C\to C\otimes_F\overline F$ is injective: choose an $F$-basis of $\overline F$ containing $1$
   and project to that coordinate. The same coordinate decomposition shows $C\otimes_F\overline
   F\ne0$. This is the coordinate ring of a nonempty affine open in the integral base change,
   hence is a domain; its subring $C$ is a domain. The identity supplies nonemptiness, so
   [def-pc-integral-scheme] proves the claim. The given isomorphism $a_F$ therefore makes $B_F$
   integral too.

3. By [lem-pc-smooth-flat], $A/T$ and $B/T$ are flat. Multiplication by $\pi$ is injective on $R$.
   At a point over the closed point, tensor this injection with the flat local ring using
   [def-weil-pbc-flat-ring-map]; at a point over the generic point, $\pi$ is a unit. Thus
   multiplication by $\pi$ is injective on every stalk of either structure sheaf
   [def-weil-flat-morphism], hence on sections of every open. For any nonempty affine
   $U=\operatorname{Spec}C$ of either scheme, the generic restriction is
   $U_F=D(\pi)=\operatorname{Spec}C[1/\pi]$. The localization map $C\to C[1/\pi]$ is injective
   since $C$ has no $\pi$-power torsion. In particular $U_F$ is nonempty and its coordinate ring
   is a domain by step 2. Hence $C$ is a domain. The identity sections and
   [def-pc-integral-scheme] now show that both $A$ and $B$ are integral, and every nonempty affine
   open meets the generic fibre. In particular the generic fibres are dense.

4. The ring $R$ is a principal ideal domain by [def-sc-discrete-valuation-ring], so
   [lem-weil-pbc-pid-noetherian-normal] makes it normal. Each $R_{\mathfrak p}$ is normal by
   [lem-weil-pbc-localization-normal-domain]; these are the local rings of $T$ by
   [lem-weil-pbc-affine-open-stalk-localization]. Apply [lem-sfb-smooth-normal-ascent] to the
   smooth map $B\to T$. Thus every local ring of the integral scheme $B$ is integrally closed.
   This uses neither excellence nor completion.

5. Choose a prime $\ell\ne\operatorname{char}k$; its image in the local ring $R$ is a unit. Set
   $E=A[\ell]$, $D=B[\ell]$, the kernels of multiplication by $\ell$. By
   [lem-sfb-smooth-group-invertible-multiplication] both are etale over $T$, and their formation
   commutes with base change. These are schemes because they are the scheme fibre products
   defining the kernels. The group homomorphism $a$ induces $u:E\to D$. Since $E$ and $D$ are
   etale over $T$, [lem-trf-space-chartwise-etale-permanence] implies $u$ is etale (take schemes
   as their represented algebraic spaces). Its kernel $L=E\times_{D,u,e_D}T$ is etale over $T$ by
   [lem-weil-pbc-etale-scheme-base-change]. The scheme $L$ is separated over $T$: $E$ is closed in
   $A$, since it is the pullback of the closed identity section of $A$ under $[\ell]_A$, and $L$
   is closed in $E$ in the same way using $D\subset B$. Identity sections of separated groups are
   closed because a section is the pullback of the diagonal. The closed-immersion base-change
   assertion applies to all these squares. Closed immersions are proper, hence separated, and
   separated morphisms compose by [lem-weil-pbc-proper-fp-permanence](c),(e).

6. The identity section $e_L:T\to L$ is also open. Indeed $L/T$ is unramified by
   [lem-sfb-space-unramified-permanence], so its diagonal is open by
   [lem-sfb-space-unramified-diagonal-open]; pulling it back along $(1_L,e_Lp):L\to L\times_TL$
   gives $e_L$. Thus $L=e_L(T)\amalg C$ for an open and closed complement $C$. On generic fibres
   $u_F$ is an isomorphism since $a_F$ is; hence $L_F=e_L(T)_F$ as schemes and $C_F=\varnothing$.
   Every stalk of $C$ is flat over the corresponding local ring of $T$, since $C$ is open in the
   etale $L$ [def-weil-etale-morphism]. If $x\in C$, its image must be the closed point and $\pi$
   is a nonzerodivisor in the nonzero local ring $\mathcal O_{C,x}$: tensor the injection
   $R\xrightarrow{\pi}R$ using [def-weil-pbc-flat-ring-map]. But $C_F=\varnothing$ says that in an
   affine neighbourhood of $x$, inverting $\pi$ gives the zero ring, so some power of $\pi$ is
   zero there, a contradiction. Therefore $C=\varnothing$ and $e_L:T\xrightarrow{\sim}L$. This
   replaces the strict-henselian lifting diagram without assuming finiteness of $B[\ell]$.

7. Let $\Omega$ be any algebraically closed extension of $k$. Put
   $K_\Omega=\ker(a_\Omega:A_\Omega\to B_\Omega)$. This is a closed subgroup of $A_\Omega$: the
   kernel is the pullback of the closed identity section of the separated group $B_\Omega$. The
   group laws restrict because $a$ preserves them. The kernel of multiplication by $\ell$ in
   $K_\Omega$ is exactly $L_\Omega$: on every test scheme both classify points of $A_\Omega$
   killed by $\ell$ and by $a_\Omega$, and the inverse fibre-product maps are induced by those
   same projections. By step 6 it is the trivial group scheme. The source $A_\Omega$ is smooth,
   separated and of finite type by base change, and is semiabelian by the hypothesis on geometric
   fibres. Apply [lem-sfb-semiabelian-closed-subgroup-trivial-torsion-finite]. It gives that
   $K_\Omega$ is finite over $\Omega$. This assertion allows a nonreduced kernel.

8. All fibres of $a$ have finite underlying sets. Generic-fibre points have singleton fibres
   because $a_F$ is an isomorphism. For a point $y$ in the special fibre of $B$, put
   $Q=A\times_B\operatorname{Spec}\kappa(y)$. If $Q$ is nonempty, choose a point $x\in Q$ and an
   algebraic closure $M$ of $\kappa(x)$. This makes $M$ an algebraically closed extension of $k$
   and supplies $z\in Q(M)$. Translation gives mutually inverse scheme maps $Q_M\to K_M$,
   $w\mapsto w-z$, and $K_M\to Q_M$, $h\mapsto h+z$: the equations $a(w-z)=a(w)-a(z)=0$ and
   $a(h+z)=y$ hold on every test scheme, and the group identities give the two inverse composites.
   By step 7, $K_M$ is finite; [lem-weil-pbc-finite-closed-map-finite-fibres](2) therefore makes
   its underlying set finite. The map $\operatorname{Spec}M\to\operatorname{Spec}\kappa(y)$ is
   surjective, so [lem-weil-pbc-surjective-base-change] makes $Q_M\to Q$ surjective. Hence $|Q|$
   is finite. Empty fibres cause no exception. Since $a$ is of finite type by step 1,
   [pqf-lem-locqf-fibre-discrete] makes it quasi-finite at every point, hence quasi-finite by
   [pqf-def-quasifinite].

9. It remains to apply Zariski Main Theorem locally on $B$. Fix a nonempty affine open $V\subseteq
   B$ and put $X=a^{-1}(V)$. Restricting a finite-type separated map to a target open preserves
   these properties by the affine definition and the diagonal pullback square; the fibres remain
   finite. Thus $f:X\to V$ satisfies [pqf-lem-normalization-open] (the target $V$ is affine, hence
   quasi-compact and quasi-separated by [lem-weil-pbc-affine-scheme-qcqs]). Write its relative
   normalization factorization as $X\xrightarrow{j}N\xrightarrow{p}V$. That node gives that $j$ is
   an open immersion and $p$ is integral. The scheme $X$ is nonempty and integral: $V_F$ is
   nonempty by step 3, $X_F\simeq V_F$, and $X$ is an open of the integral $A$. Clause (iv) of
   [lem-weil-pbc-relative-normalization] therefore makes $N$ integral. The open $j(X)$ is
   nonempty, hence dense in integral $N$.

10. The common nonempty opens $X_F\subseteq X$ and $V_F\subseteq V$ are isomorphic via $f_F$.
   Consequently $f$ maps the generic point of $X$ to that of $V$ and induces an isomorphism on
   their local rings. Since $j$ is an open immersion of nonempty integral schemes, it maps the
   generic point of $X$ to that of $N$ and induces an isomorphism on those same generic local
   rings. The identity $p\circ j=f$ therefore shows that $p$ maps the generic point of $N$ to that
   of $V$ and induces an isomorphism of function fields (generic local rings)
   [lem-sc-integral-function-field-affine-fraction]. Normality of $B$ from step 4 gives normal
   local rings on $V$. Apply [lem-trf-integral-birational-normal-isomorphism] to $p:N\to V$: it is
   an isomorphism. Thus $f=p\circ j$ identifies $X$ with an open subscheme of $V$. These
   identifications over affine opens of $B$ agree on intersections, because they are restrictions
   of the single map $a$; their inverses agree by uniqueness of inverses. They glue to an
   identification of $A$ with the open union of their images in $B$. By [def-weil-open-immersion],
   $a$ is an open immersion.
-/
theorem isOpenImmersion_of_generically_isomorphic_semiabelian
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (F : Type u) [Field F] [Algebra R F] [IsFractionRing R F]
    (A B : Grp (Over (Spec (.of R)))) [IsCommMonObj A.X] [IsCommMonObj B.X]
    [Smooth A.X.hom] [IsSeparated A.X.hom]
    [LocallyOfFinitePresentation A.X.hom] [QuasiCompact A.X.hom]
    [Smooth B.X.hom] [IsSeparated B.X.hom]
    (hA : HasSemiabelianGeometricFibres A) (a : A ⟶ B)
    (hgeneric : IsIso
      (((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))).map a.hom.hom).left)) :
    IsOpenImmersion a.hom.hom.left := by
  sorry

end AlgebraicGeometry
