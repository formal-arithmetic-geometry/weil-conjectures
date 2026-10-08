+++
id = "sk-i-real-compactification"
kind = "section"
title = "Smooth proper completion"
order = 2611
uses = ["sk-d-real-setup", "sk-thm-nagata-compactification"]
lean = ["AlgebraicGeometry.exists_smooth_properCompactification"]
+++
*Proposition (sketch).*

Every smooth geometrically connected curve
$U_0/\Fq$ has a smooth proper completion $U_0\hookrightarrow C_0$ over
$\Fq$ whose boundary $C_0\setminus U_0$ is a finite set of closed points,
and $C_0$ is again geometrically connected.

## Proof

*Step 1 (compactify).* Being smooth and geometrically connected,
$U_0$ is integral. [sk-thm-nagata-compactification] gives an open immersion of $U_0$
into a scheme proper over $\Fq$; replace that scheme by the
scheme-theoretic closure $X$ of $U_0$ in it. A closed subscheme of a
proper scheme is proper, $U_0\hookrightarrow X$ is a dense open immersion,
$X$ is integral, and $\dim X=\dim U_0=1$.

*Step 2 (the boundary is finite).* $X\setminus U_0$ is a proper
closed subset of the integral one-dimensional $X$, hence of dimension zero,
hence a finite set of closed points, $X$ being of finite type over $\Fq$.

*Step 3 (normalize).* Let $\nu:C_0=X^{\nu}\to X$ be the
normalization of $X$ in the function field of $U_0$. For an integral
scheme of finite type over a field this $\nu$ is finite, surjective and
birational, so $C_0$ is again proper over $\Fq$ of dimension one, and
$\nu$ is an isomorphism over the normal locus of $X$.

*Step 4 (the completion is smooth).* $C_0$ is normal of dimension
one, hence regular, and a regular scheme of finite type over the perfect
field $\Fq$ is smooth
([Stacks `00TV`](https://stacks.math.columbia.edu/tag/00TV)).

*Step 5 (the open immersion and its boundary).* $U_0$ is smooth,
hence normal, hence contained in the normal locus of $X$, so $U_0\to C_0$
is an open immersion by Step 3. Its complement is
$\nu^{-1}(X\setminus U_0)$, the preimage of a finite set under a finite
morphism, hence finite.

*Step 6 (geometric connectedness).* By [sk-d-real-setup] the
base change $U=U_0\times_{\Fq}k$ is connected, and it is dense in
$C_0\times_{\Fq}k$; a scheme with a dense connected open subscheme is
connected, since each part of a separation would have to meet that open.

Steps 1–5 are the argument of Blueprint 06,
`lem-sc-compactification`, whose normalization package is
`lem-sc-normalization-properties`(a)–(c); it is stated there
over an algebraically closed field, but no step uses algebraic closedness.

Uses: [sk-d-real-setup], [sk-thm-nagata-compactification]
