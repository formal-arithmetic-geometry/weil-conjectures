+++
id = "lem-weil-derived-direct-image-composition"
kind = "lemma"
title = "Composition of derived direct images"
order = 1470
uses = ["def-weil-algebraically-closed-coefficients", "def-weil-derived-complete", "def-weil-derived-complete-integral-detailed", "def-weil-derived-direct-image", "def-weil-derived-limit", "def-weil-derived-pullback-tensor-hom", "def-weil-pbc-kinjective-resolutions", "def-weil-rationalization-karoubi", "lem-sp-kinjective-computes", "lem-weil-pbc-direct-image-preserves-injectives", "lem-weil-restriction-of-scalars-exact", "lem-weil-scalar-extension-composition"]
+++
Let $X\xrightarrow{f}Y\xrightarrow{g}Z$ be morphisms of schemes on which
$\ell$ is invertible, and use the derived direct images of
[def-weil-derived-direct-image]. There is a canonical isomorphism

$$
 c_{g,f}:R(g\circ f)_*\xrightarrow{\ \sim\ }Rg_*\circ Rf_*
$$

at each coefficient stage of that definition:

1. at finite level $A_{E,n}$, as functors
$D(X_{\mathrm{proet}},A_{E,n})\to D(Z_{\mathrm{proet}},A_{E,n})$;
1. for $\Lambda=\mathcal O_E$, on those $K\in D^b_c(X,\mathcal O_E)$ with
$Rf_*K\in D^b_c(Y,\mathcal O_E)$ (so that the right side is defined);
1. for $\Lambda=E$, on the rationalized category of
[def-weil-rationalization-karoubi], for the same $K$;
1. for $\Lambda=\Qlb$, on the common-stage category of
[def-weil-algebraically-closed-coefficients], for objects $(E,K)$ with $K$
as in (3);
1. on the small étale site, for any ring $A$, as functors
$D(X_{\mathrm{et}},A)\to D(Z_{\mathrm{et}},A)$ between the ordinary
derived categories of étale sheaves of $A$-modules.

The isomorphism $c_{g,f}$ is natural in $K$, is the identity when $f$ or $g$
is an identity, and is associative: for a further morphism $h:Z\to W$ the
two isomorphisms $R(hgf)_*\cong Rh_*Rg_*Rf_*$ built from $c$ agree. In
particular it is compatible with transport of structure along automorphisms
of $X,Y,Z$ commuting with $f$ and $g$ (such as Frobenius), since the direct
image along an automorphism $\sigma$ is the inverse image along
$\sigma^{-1}$.

## Proof

*Finite level.* Put $A=A_{E,n}$. The constant sheaves satisfy
$f^{-1}A_Y=A_X$, so the sheaf-level inverse image $f^{-1}$ of
[def-weil-derived-pullback-tensor-hom] is an exact left adjoint of
$f_*:\Sh(X_{\mathrm{proet}},A)\to\Sh(Y_{\mathrm{proet}},A)$. Hence $f_*$
carries K-injective complexes [def-weil-pbc-kinjective-resolutions] to
K-injective complexes: for an acyclic $B$ one has
$\operatorname{Hom}(B,f_*I)=\operatorname{Hom}(f^{-1}B,I)$, and $f^{-1}B$ is
acyclic. This is the argument of
[lem-weil-pbc-direct-image-preserves-injectives], applied to complexes and
on the pro-etale site. If $K\to I$ is a K-injective resolution, then $f_*I$
is a K-injective complex computing $Rf_{*,n}K$, so
$Rg_{*,n}Rf_{*,n}K=g_*f_*I=(gf)_*I=R(gf)_{*,n}K$. By the well-definedness
and functoriality of K-injective resolutions
([lem-sp-kinjective-computes], part (1)), the resulting isomorphism does not
depend on $I$ and is natural in $K$. Identity and associativity hold because
$(hg)f=h(gf)$ already holds for the sheaf-level functors on the same
representative $I$. The same argument applies verbatim on the small étale site with any
coefficient ring (item (5)) and to sheaves of abelian groups, and for $\widehat{\mathcal O}_E$-modules it gives the composition
isomorphism for the derived functor $Rh^{\wedge}_*$ of
$h_*:\Sh(-,\mathcal O_E)\to\Sh(-,\mathcal O_E)$ in the following form. The
derived direct image of modules over a sheaf of rings is computed on the
underlying abelian sheaves, since a K-injective complex of modules is K-limp
and so acyclic for the direct image of abelian sheaves. The canonical map
$R(gf)^{\wedge}_*\to Rg^{\wedge}_*Rf^{\wedge}_*$ given by the universal
property of right derived functors therefore becomes the abelian-sheaf
isomorphism after the forgetful functor to abelian sheaves. That functor
reflects isomorphisms, so the map is an isomorphism.

*Integral stage.* Let $h$ be any of $f,g,gf$ and let $K$ be derived complete
[def-weil-derived-complete]. First, $Rh^{\wedge}_*$ commutes with
$\operatorname{Res}_n$: the functor $\operatorname{Res}_n$ is exact
([lem-weil-restriction-of-scalars-exact]) and commutes with $h_*$ on sheaves.
Both $\operatorname{Res}_nRh_{*,n}$ and $Rh^{\wedge}_*\operatorname{Res}_n$
are computed on underlying abelian sheaves by the previous paragraph, so the
canonical comparison
$\operatorname{Res}_nRh_{*,n}\to Rh^{\wedge}_*\operatorname{Res}_n$ is an
isomorphism. Second, $Rh^{\wedge}_*$ commutes with countable products,
because a product of K-injective complexes is K-injective and $h_*$
commutes with products termwise. It is also exact, so it carries the Roos
triangle of [def-weil-derived-limit] for the system
$(\operatorname{Res}_nK_n)$ to a Roos triangle for
$(Rh^{\wedge}_*\operatorname{Res}_nK_n)$. Combining these facts with
derived completeness $K\xrightarrow{\sim}R\varprojlim_n\operatorname{Res}_nK_n$
gives

$$
 Rh_*K=R\varprojlim_n\operatorname{Res}_nRh_{*,n}K_n
 \cong R\varprojlim_nRh^{\wedge}_*\operatorname{Res}_nK_n
 \cong Rh^{\wedge}_*R\varprojlim_n\operatorname{Res}_nK_n
 \cong Rh^{\wedge}_*K ,
$$

so the direct image of [def-weil-derived-direct-image] is the derived functor
$Rh^{\wedge}_*$ on derived-complete objects. For $K\in D^b_c(X,\mathcal O_E)$
with $Rf_*K\in D^b_c(Y,\mathcal O_E)$, both $K$ and $Rf_*K$ are derived
complete ([def-weil-derived-complete-integral-detailed]). Applying this
identification for $h=gf$, $f$ and $g$ therefore gives

$$
 R(gf)_*K\cong R(gf)^{\wedge}_*K\cong Rg^{\wedge}_*Rf^{\wedge}_*K
 \cong Rg_*Rf_*K,
$$

the middle step being the composition isomorphism for $\widehat{\mathcal
O}_E$-modules. Naturality, identity and associativity are inherited from the
module level.

*Rational stage.* By [def-weil-rationalization-karoubi], $D^b_c(-,E)$ has the
same objects as $D^b_c(-,\mathcal O_E)$ and
$\operatorname{Hom}\otimes_{\mathcal O_E}E$ as morphisms, and $Rf_*$ on it is
the $\mathcal O_E$-linear integral functor followed by $-\otimes_{\mathcal
O_E}E$ on morphisms. The integral isomorphism $c_{g,f}$ is a natural
isomorphism of $\mathcal O_E$-linear functors, so its image is a natural
isomorphism of the rationalized functors. The identity and associativity
equations are preserved.

*Algebraically closed stage.* In the common-stage category of
[def-weil-algebraically-closed-coefficients], an object $(E,K)$ has direct
image $(E,Rf_*K)$, and a morphism is represented at some finite $L\supset E$
after scalar extension. Take $c_{g,f}$ at stage $E$ on objects. It is
compatible with scalar extension to $L$, which is what naturality for
morphisms represented at $L$ requires. Indeed, on integral representatives
$-\otimes_{\mathcal O_E}\mathcal O_L$ is, as an $\widehat{\mathcal
O}_E$-module, a finite direct sum of copies of the identity ($\mathcal O_L$
being finite free over $\mathcal O_E$). The derived functors $Rh^{\wedge}_*$
and the composition isomorphism commute with finite direct sums and with the
forgetful functors along $\widehat{\mathcal O}_E\to\widehat{\mathcal O}_L$,
since all of them are computed on underlying abelian sheaves. The iterated
extensions agree by [lem-weil-scalar-extension-composition]. Hence $c_{g,f}$
at stage $E$ and at stage $L$ correspond under scalar extension, giving a
natural isomorphism in $D^b_c(Z,\Qlb)$ with the stated identity and
associativity properties.

Finally, for an automorphism $\sigma$ the direct image $R\sigma_*$ is
inverse to $R(\sigma^{-1})_*$ by the identity and associativity properties.
An automorphism of the diagram $X\to Y\to Z$ therefore transports $c_{g,f}$
to itself by associativity, which is the asserted compatibility with
transport of structure.
