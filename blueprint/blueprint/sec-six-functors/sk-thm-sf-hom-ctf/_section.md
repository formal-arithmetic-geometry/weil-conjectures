+++
id = "sk-thm-sf-hom-ctf"
kind = "section"
title = "Internal Hom with finite Tor amplitude"
order = 2196
uses = ["sk-def-sf-admissible", "sk-def-sf-operations", "sk-prop-sf-biduality-general", "sk-prop-sf-existence", "sk-prop-sf-finiteness", "sk-prop-sf-fullcd-etale-origin", "sk-prop-sf-rf-shriek-preservation"]
lean = ["AlgebraicGeometry.Etale.boundedConstructible_derivedHom", "AlgebraicGeometry.Etale.torAmplitudeIn_derivedHom", "AlgebraicGeometry.Etale.torAmplitudeIn_derivedHom_of_isDualizable"]
+++
*Theorem (sketch).*

Let $A=A_{E,n}$, let $X$ be a finite-type $k$-scheme with $\dim X\le m$, and
let $K,M$ be bounded constructible $A$-complexes on $X_{\Et}$ with finite Tor
amplitude in $[a,b]$ and in $[c,d]$. No admissibility datum on the
structure morphism $a_X$ is assumed: the general interval rests on
[sk-prop-sf-biduality-general], whose dualizing complex is formed with the
unconditional constructible adjoint $Ra_X^!$ of [sk-def-sf-operations] (vi)
— [sk-prop-sf-existence] (a) gives the étale adjoint of $Ra_{X!}$ for
the compactifiable $a_X$ between Noetherian schemes, (c) transports it to
$\Dctf$, and the preservation clauses are
[sk-prop-sf-rf-shriek-preservation] ([sk-rem-sf-fullcd-scope]). Then
$\RHom_A(K,M)$ is bounded constructible with finite Tor amplitude in
$[c-b-2m,d-a+2m]$. If $K$ is site-perfect (locally on $X_{\Et}$ a bounded
complex of finite projective $A$-modules in degrees $[a,b]$), the sharper
interval $[c-b,d-a]$ holds, and no duality at all is needed for it. The
sharper interval fails for general $K$: for
the origin $i:\{0\}\hookrightarrow\mathbf A^1$ the complexes $i_*A$ and $A$
have Tor amplitude $[0,0]$, but $\RHom_A(i_*A,A)=i_*A(-1)[-2]$.

## Proof

Constructibility: every cohomology sheaf of $\RHom_A(K,M)$ is constructible,
because the $\mathcal Ext$-sheaves of two constructible complexes are
constructible on a common stratification. Site-perfect case: locally
$K$ is a bounded complex $P$ of finite projective $A$-modules in $[a,b]$, so
$\RHom_A(K,M)=P^\vee\otimes^L_AM$ locally, a bounded flat complex in
$[c-b,d-a]$; since stalks are exact and conservative on the étale site the
interval holds globally. General case: the stalk of $\RHom$ is *not*
$\RHom$ of the stalks (the example above), and one argues geometrically. By
[sk-prop-sf-biduality-general] — applied to $a_X$, with the
unconditional $Ra_X^!$ — and the tensor–Hom adjunction,
$\RHom_A(K,M)\cong\mathbb D_X(K\otimes^L_A\mathbb D_XM)$, and $\mathbb D_X$
carries Tor amplitude $[c,d]$ into $[-d-2m,-c]$ (the dualizing complex has
cohomology in $[-2m,0]$). Applying this twice, with the additivity of Tor
amplitude for $\otimes^L$, gives $[c-b-2m,d-a+2m]$.

Uses: `\Cref{sk-prop-sf-biduality-general}`, `\Cref{sk-prop-sf-finiteness}`, `\Cref{sk-def-sf-admissible}`, `\Cref{sk-prop-sf-existence}`, `\Cref{sk-prop-sf-fullcd-etale-origin}`, `\Cref{sk-prop-sf-rf-shriek-preservation}`, `lemma-weil-pbc-geometric-stalk-conservative`
