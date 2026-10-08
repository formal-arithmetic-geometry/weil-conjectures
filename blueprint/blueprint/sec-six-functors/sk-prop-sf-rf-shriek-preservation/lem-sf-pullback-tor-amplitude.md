+++
id = "lem-sf-pullback-tor-amplitude"
kind = "lemma"
title = "Pullback preserves finite Tor amplitude"
order = 2064
uses = ["def-weil-derived-pullback-tensor-hom", "def-weil-derived-tensor", "def-weil-finite-tor-amplitude", "def-weil-finite-torsion-constructibility", "def-weil-pbc-proetale-site", "def-weil-scheme-morphism-properties", "lem-exc-constant-inverse-image-flat", "lem-sf-flat-model", "lem-weil-pbc-pullback-preserves-bounded-constructible"]
+++
Fix the global finite-field datum, a prime $\ell\ne p$, $n\geq1$, and
put $A=A_{E,n}$. Let $f:X\to Y$ be a
separated finite-type
morphism of finite-type $k$-schemes, and let $K\in D^b_c(Y,A)$ be a
bounded constructible
complex of finite Tor amplitude
in $[a,b]$. Then $Lf^*K\in D^b_c(X,A)$ is bounded constructible and has
finite Tor amplitude in $[a,b]$. Consequently $Lf^*$ carries
$D^b_{ctf}(Y,A)$ into $D^b_{ctf}(X,A)$, which is clause (i) of
the finite-Tor preservation summary at the finite coefficient stages.

## Proof

Bounded constructibility is
[lem-weil-pbc-pullback-preserves-bounded-constructible], which also
gives that the cohomological interval is preserved. For the Tor bound apply
[lem-sf-flat-model] to $K$: there is an isomorphism $K\cong P$ in
$D(Y_{\mathrm{proet}},A)$ with $P$ a bounded complex of flat
$A_Y$-module sheaves, $P^q=0$ for $q\notin[a,b]$. By
[def-weil-derived-pullback-tensor-hom] one has
$Lf^*K=f^{-1}K\otimes_{f^{-1}A}^LA$, and $f^{-1}A=A$; since inverse
image is exact the map $f^{-1}P\to f^{-1}K$ is a quasi-isomorphism, and
$f^{-1}P$ is a bounded complex of flat $A_X$-module sheaves, hence
K-flat, so $Lf^*K\cong f^{-1}P$ by [def-weil-derived-tensor]. The
inverse image of a flat sheaf is flat, as follows:
$f^{-1}G'\to f^{-1}G$ is injective
for an injection $G'\to G$ by exactness, and inverse image commutes with
tensor products of module sheaves, so
$f^{-1}F\otimes_Af^{-1}G'\to f^{-1}F\otimes_Af^{-1}G$ is the functor
$f^{-1}$ applied to $F\otimes_AG'\to F\otimes_AG$, which is injective
because $F$ is flat; flatness is understood as in
[lem-exc-constant-inverse-image-flat]. Hence for every sheaf $N$ of
$A_X$-modules in degree zero the complex
$Lf^*K\otimes_A^LN\cong(f^{-1}P)\otimes_AN$ has terms only in degrees
$[a,b]$, each term $f^{-1}P^q\otimes_AN$ lying in degree $q$ because
$f^{-1}P^q$ is flat. Therefore
$\mathcal H^r(Lf^*K\otimes_A^LN)=0$ for $r\notin[a,b]$ for every such
$N$, which is the finite Tor amplitude of $Lf^*K$ in $[a,b]$ in the
sense of [def-weil-finite-tor-amplitude].
