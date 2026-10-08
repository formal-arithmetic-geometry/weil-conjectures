+++
id = "sk-rem-sf-typing"
kind = "section"
title = "Typing table: ambient definition, small-category theorem"
order = 2044
+++
*Remark (sketch).*

For each operation the second column is where it is *defined*, the third
where it is *proved* to descend, with the statement that proves it.
$\Dbc,\Dctf,D_c^{[a,b]}$ are as in [sk-def-sf-categories]; ``ét'' and
``proét'' refer to the small étale and the small pro-étale site.

| operation | ambient definition | descent to small categories (theorem) |
| --- | --- | --- |
| $Lf^*$ | $D(Y,\Lambda)\to D(X,\Lambda)$ | $\Dbc(Y)\to\Dbc(X)$ ([sk-prop-sf-finiteness], ét); $\Dctf(Y)\to\Dctf(X)$ ([sk-thm-sf-ctf-stability] (i)) |
| $-\otimes^L-$ | $D(Y)^2\to D(Y)$ | $\Dctf\times\Dbc\to\Dbc$ and $\Dctf\times\Dctf\to\Dctf$ on ét and proét, with $[a,b]+[c,d]\mapsto[a+c,b+d]$ ([sk-thm-sf-ctf-stability] (ii)) |
| $\RHom(-,-)$ | $D(Y)^{\mathrm{op}}\times D(Y)\to D(Y)$ | $\Dctf\times\Dctf\to\Dctf$ on ét for two arbitrary objects, and on proét for pulled-back pairs, with $[a,b],[c,d]\mapsto[c-b-2m,d-a+2m]$ ($\dim Y\le m$), and $[c-b,d-a]$ for a site-perfect first argument ([sk-thm-sf-hom-ctf], [sk-thm-sf-ctf-stability] (ii)) |
| $Rf_*$ | $D^+(X)\to D^+(Y)$ | $\Dbc(X)\to\Dbc(Y)$ for every finite-type $f$ ([sk-prop-sf-finiteness]); $\Dctf(X)\to\Dctf(Y)$ on ét and proét, with $[a,b]\mapsto[a,b+2\dim X]$ for $f:X\to Y$ of finite-type $k$-schemes, $k=\overline{\mathbf F}_q$ ([sk-thm-sf-direct-image-tor-amplitude], [sk-cor-sf-direct-image-ctf], [sk-thm-sf-ctf-stability] (iii)) |
| $Rf_!$ | ambient, via a compactification | $\Dbc(X)\to\Dbc(Y)$ ([sk-prop-sf-finiteness]) and $\Dctf(X)\to\Dctf(Y)$ ([sk-thm-sf-ctf-stability] (iv)) |
| $Rf^{\times}$ | $D(Y)\to D(X)$, right adjoint of $Rf_!$; *hypothetical*: assumed to exist under the ambient datum, which fails in general ([sk-rem-sf-fullcd-scope]) | none, and none is needed: it is an optional ambient functor used nowhere downstream. [sk-prop-sf-existence] proves the adjoint exists on the étale sites unconditionally (a); its pro-étale form (b) is conditional on a hypothesis that is false in general |
| $Rf^!$ | *defined* on $\Dctf(Y,\Lambda)$ as $\nu_X^*f^{\times}R\nu_{Y,*}$, the étale adjoint of [sk-prop-sf-existence] (a) transported along the comparison ([sk-def-sf-operations] (vi), [sk-prop-sf-existence] (c)) | $\Dctf(Y)\to\Dctf(X)$ for *every* separated finite-type $f$ of finite-type $k$-schemes, with no admissibility hypothesis; shifts $[a,b]\mapsto[a-2d,b-2d]$ for $f$ smooth of pure relative dimension $d$, $[a,b]\mapsto[a,b+2d+1]$ for a closed immersion into a target of dimension $\le d$ (a target-dimension bound; no codimension-only bound is asserted), and $[a,b]\mapsto[a-2D,b+2\dim Y+1]$ in general, $D$ the maximal embedding dimension of the affine charts ([sk-prop-sf-rf-shriek-preservation], [sk-thm-sf-ctf-stability] (v)) |
| $\mathbb D_X$ | $D(X)^{\mathrm{op}}\to D(X)$, $\RHom_X(-,\omega_X)$ | $\Dctf(X)\to\Dctf(X)$, a contravariant anti-equivalence, for every separated finite-type $X$ ([sk-prop-sf-biduality-general], [sk-thm-sf-ctf-stability] (vi)) |

The table is an enumeration: every entry is a theorem of the blueprint, and
the conditional entries are listed in [sk-rem-sf-ledger].
