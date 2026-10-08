+++
id = "sk-lem-finite"
kind = "section"
title = "Finiteness: the global sections are perfect at the point"
order = 2426
uses = ["sk-def-perfect", "sk-def-set", "sk-prop-sf-trace-perfectness", "sk-thm-sf-ctf-stability", "sk-thm-sf-direct-image-tor-amplitude"]
+++
*Lemma (sketch).*

In the setting of [sk-def-set], for $K\in\Dctf(X,\Lambda)$, the
perfectness of $\RGammac(X,K)$ at finite coefficients in
[sk-prop-sf-trace-perfectness] extends to $\Oe,E,\Qlb$.
At every coefficient stage, $\RGamma(X,K)$ and the duals of both
ordinary and compactly supported cohomology are also perfect point
complexes: bounded with finite cohomology of finite Tor amplitude
at finite level, with one common amplitude over $\Oe$, bounded with
finite-dimensional cohomology at the field stages. (Blueprint 9,
sbc-thm-finiteness-finite-type and obl:fin-comparison, the finiteness
chain of the smooth-base-change chapter; the interface is
prop:cohomological-finiteness of 1, whose verification proof
assembles that chain, and the point-complex form is
thm:pod-point-perfectness.)

## Proof

*Step 1 (finite level).* Let $\Lambda=A_{E,n}$ and let $K$ be a
bounded constructible complex of finite Tor amplitude. The structure
morphism $a_X$ is separated of finite type over the field $k$, so the
finiteness chain of 9 applies: the sheaves $R^qa_{X,*}K$ and
$R^qa_{X,!}K$ are constructible and, if the cohomology sheaves of $K$
lie in degrees $[a,b]$, both vanish for $q\notin[a,b+2\dim X]$: the
compact-support ones by sbc-thm-finiteness-finite-type and
obl:fin-comparison, the ordinary ones by the cohomological-dimension
bound fin4-lem-fibrewise-cohomological-dimension, each applied to the
cohomology sheaves of $K$ through the spectral sequence of the truncations
(for $K=\Lambda[-1]$ on a point the bound is $1$, not $2\dim X=0$).
At the geometric point $s$ a constructible complex is a bounded complex of
finite modules (def:weil-finite-coefficient-point), so
$\RGammac(X,K)$ and $\RGamma(X,K)$ are bounded with finite cohomology.
*Step 2 (perfectness over the Noetherian ring).* Over $A=\AEn$, a
bounded complex with finite cohomology and finite Tor amplitude is
represented by a bounded complex of finite projective modules: take a
bounded-above resolution by finitely generated free modules, truncate it in
degrees at least the lower amplitude bound, and observe that the resulting
cokernel is finitely presented of Tor-dimension zero, hence flat, hence
projective, finitely presented flat modules over a Noetherian ring being
projective. This is fix-lem-finite-tor-perfect and is the elementary
part of prop:trf-compact-support-perfectness.
*Step 3 (the stages and the duals).* The uniform-tower reconstruction
places $\RGammac(X,K)$ in $D^b_{\mathrm{fg}}(\Oe)$ with perfect
reductions of one common amplitude
(lem:weil-pbc-reconstruction-uniform-tower). The same holds for
$\RGamma(X,K)$: choose a compactification $j:X\hookrightarrow\bar X$
of the separated finite-type $k$-scheme $X$, as in the definition of
$Rf_!$ in [sk-def-ops]. Then
$Ra_{X*}=Ra_{\bar X*}Rj_*=Ra_{\bar X!}Rj_*$, $\bar X$ being proper,
i.e. $\RGamma(X,K)=\RGammac(\bar X,Rj_*K)$; and $Rj_*$ carries
$\Dctf(X,\Lambda)$ to $\Dctf(\bar X,\Lambda)$, with Tor amplitude
$[a,b]\mapsto[a,b+2\dim X]$, compatibly with the finite reductions
([sk-thm-sf-direct-image-tor-amplitude];
[sk-thm-sf-ctf-stability](iii),(vii)). So $(Rj_*K_n)_n$ is again a
normalized system with common bounds on the proper $\bar X$, and the
compact-support case just proved, applied to $\bar X$ and $Rj_*K$,
places $\RGamma(X,K)$ in $D^b_{\mathrm{fg}}(\Oe)$ with perfect
reductions of one common amplitude. The rational and algebraically closed
stages of $\RGammac$ and $\RGamma$ follow by flat extension of scalars
([sk-def-ops]); the dual of a bounded complex of finite projective modules
is again one, termwise. This is the point-perfectness
thm:pod-point-perfectness of 15, and it is assembled from the
finiteness interface prop:cohomological-finiteness of 1.

Uses: [sk-def-perfect], [sk-def-set], [sk-prop-sf-trace-perfectness]
