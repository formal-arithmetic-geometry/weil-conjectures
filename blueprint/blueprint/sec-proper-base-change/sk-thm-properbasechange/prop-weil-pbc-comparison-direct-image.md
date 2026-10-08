+++
id = "prop-weil-pbc-comparison-direct-image"
kind = "theorem"
title = "Comparison direct image"
order = 1291
uses = ["def-weil-pbc-direct-image", "def-weil-pbc-proetale-operations", "def-weil-pbc-scheme-conventions", "def-weil-pbc-site-comparison-morphism", "lem-weil-pbc-basis-derived-detection", "lem-weil-pbc-comparison-global-cohomology", "lem-weil-pbc-comparison-injective-acyclicity", "lem-weil-pbc-comparison-pullback", "lem-weil-pbc-comparison-sections", "lem-weil-pbc-derived-cohomology-continuity", "lem-weil-pbc-etale-restriction-injectives", "lem-weil-pbc-proetale-restriction-injectives", "prop-weil-pbc-inverse-image-exact", "prop-weil-pbc-proetale-constant-exact"]
tags = ["latex:proposition"]
+++
Let $u:U\to V$ be quasi-compact and quasi-separated and let
$L\in\Dplus(U_{\Et},\Lambda)$. There is a natural isomorphism

$$
 \nu_V^*Ru_{\Et,*}L
 \xrightarrow{\sim}
 Ru_{\Proet,*}\nu_U^*L.
$$

It is compatible with identities, composites, and morphisms of $L$.

## Proof

Specify the map before proving it invertible. By the pullback identification
of [lem-weil-pbc-comparison-pullback], the counit for the etale adjunction
gives

$$
 u_{\Proet}^*\nu_V^*Ru_{\Et,*}L
 \simeq\nu_U^*u_{\Et}^*Ru_{\Et,*}L
 \longrightarrow\nu_U^*L.
$$

Its mate under the adjunction of the pro-etale operations is the map
$\alpha_L$ in the statement. Both sides are bounded below; inverse images are
exact and right derived direct images preserve lower bounds.

The assertion is local on $V$, so take $V$ affine. Let $W=\varprojlim_i W_i$
be an arbitrary affine ind-etale basis object, with $W_i\to V$ affine etale
of finite presentation, and put $U_i=U\times_VW_i$, $U_W=U\times_VW$. The
schemes $U_i$ are quasi-compact and quasi-separated because $u$ is, and their
transition maps are affine. Pullback compatibility and
[lem-weil-pbc-comparison-global-cohomology] identify the degree-$n$ derived
sections of the source with

$$
 H^nR\Gamma\bigl(W_{\Et},(Ru_{\Et,*}L)|_W\bigr).
$$

Apply the continuity of derived cohomology first on $W=\varprojlim_iW_i$ and
then on $U_W=\varprojlim_iU_i$. They give the two outer identifications in

$$
 \begin{split}
 H^nR\Gamma\bigl(W_{\Et},(Ru_{\Et,*}L)|_W\bigr)
 &\simeq\varinjlim_i
       H^nR\Gamma\bigl(W_{i,\Et},(Ru_{\Et,*}L)|_{W_i}\bigr)\\
 &\simeq\varinjlim_i H^nR\Gamma(U_{i,\Et},L|_{U_i})\\
 &\simeq H^nR\Gamma(U_{W,\Et},L|_{U_W}).
 \end{split}
$$

The middle identification is derived evaluation of the direct image. Indeed
an injective resolution on $U_{\Et}$ restricts to an injective resolution on
$U_i$ by the etale-restriction lemma; direct image preserves injectives since
its inverse image is exact. Evaluation of that resolution gives precisely the
same section complex on the two sides.

By [lem-weil-pbc-comparison-global-cohomology], the last group is
$H^nR\Gamma(U_{W,\Proet},(\nu_U^*L)|_{U_W})$. By
[lem-weil-pbc-proetale-restriction-injectives], this in turn is

$$
 H^nR\Gamma(W_{\Proet},Ru_{\Proet,*}\nu_U^*L),
$$

the derived sections of the target. For this last equality use a pro-etale
injective resolution on $U$; its restriction to $U_W$ is injective, and its
direct image is injective because $u_{\Proet}^*$ is exact.

We check that the isomorphism just calculated is induced by $\alpha_L$.
Represent $L$ by an etale injective complex $I^\bullet$, and resolve
$\nu_U^*I^\bullet$ by a pro-etale injective complex $J^\bullet$. The mate is
represented by the map $\nu_V^*u_{\Et,*}I^\bullet\to u_{\Proet,*}J^\bullet$
adjoint to the pulled-back counit followed by $\nu_U^*I^\bullet\to
J^\bullet$. Each $u_{\Et,*}I^r$ is injective on $V_{\Et}$. Hence
[lem-weil-pbc-comparison-injective-acyclicity] makes $\nu_V^*u_{\Et,*}I^r$
acyclic for sections on every basis object $W$. Bounded-below acyclic
resolutions thus allow derived sections of the source to be computed by
evaluating this very complex; the target complex is already injective.
Moreover [lem-weil-pbc-comparison-sections] identifies its source section
complex with $\varinjlim_i\Gamma(U_i,I^\bullet)$. This justifies checking the
named map on these models. At a finite stage $W_i$, evaluation of that counit
is the identity on sections of $I^\bullet$ on $U_i$. Restricting to $W$ gives
exactly the canonical restriction from $U_i$ to $U_W$ followed by the global
cohomology comparison. The identifications above are natural in these
restriction maps. On taking the filtered colimit they therefore compute
$H^nR\Gamma(W,\alpha_L)$, not an unspecified isomorphism between the same
groups.

Thus $\alpha_L$ is an isomorphism on derived sections of every basis object,
in every degree. [lem-weil-pbc-basis-derived-detection] proves it is an
isomorphism of complexes. For identity morphisms its defining mate is the
identity. For a composite, the counit is the composite of the two counits
after the usual associativity identifications; applying the displayed mate
formula gives the composite of the two comparison maps. The triangle
identities remove the inserted unit--counit pairs. This proves the
composition law, while naturality in $L$ follows from naturality of the
counit and the coherent pullback identification. See
[Stacks Project, Section 61.19](https://stacks.math.columbia.edu/tag/099R)
for the comparison's standard setting.
