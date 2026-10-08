+++
id = "lem-trf-global-operator-perfect"
kind = "lemma"
title = "The global operator is an endomorphism of a perfect complex"
order = 2290
uses = ["def-compact-support-direct-image-detailed", "def-trf-admissibility", "def-trf-categorical-trace", "def-trf-coefficient-conventions", "def-trf-correspondence", "def-trf-global-operator", "def-weil-exceptional-adjoint-admissibility", "def-weil-finite-tor-amplitude", "prop-trf-compact-support-perfectness"]
+++
Fix the coefficient
conventions, let $c=(c_1,c_2):C\to X\times_sX$ be an
admissible cohomological
correspondence whose ordinary leg $c_2$ is
proper, and let
$K\in D^b_{ctf}(X,A)$ with correspondence
$u:Lc_2^*K\to Rc_1^!K$. Then the global operator $T_c(u)$ of
[def-trf-global-operator] is a morphism of
$D^b_{\mathrm{fin}}(A)$ in the sense of
[def-trf-categorical-trace]: every intermediate complex of the
composite defining $T_c(u)$ is compact-support cohomology of a
finite-Tor constructible
complex.

## Proof

By [def-trf-coefficient-conventions] the source and the target of
$T_c(u)$ are $R\Gamma_c(X,K)$, which lies in
$D^b_{\mathrm{fin}}(A)$ by
[prop-trf-compact-support-perfectness], and
$D^b_{\mathrm{fin}}(A)$ of [def-trf-categorical-trace] is a
full subcategory of $D(A)$, so it
suffices to see that the composite of
[def-trf-global-operator] is formed in
$D^b_{\mathrm{fin}}(A)$, i.e. that its intermediate complexes are
compact-support cohomology of finite-Tor constructible complexes in
the sense of [def-weil-finite-tor-amplitude]:
$Lc_2^*K$ is finite-Tor constructible, so
$R\Gamma_c(C,Lc_2^*K)\in D^b_{\mathrm{fin}}(A)$; the identification
$Rc_{2*}\cong Rc_{2!}$ for the proper $c_2$ shows that
$Rc_{2*}Lc_2^*K\cong Rc_{2!}Lc_2^*K$ is finite-Tor constructible as
well, so $R\Gamma_c(X,Rc_{2*}Lc_2^*K)\in D^b_{\mathrm{fin}}(A)$;
finally $Rc_1^!K$ is finite-Tor constructible by item (3) of
[def-weil-exceptional-adjoint-admissibility], as required by the
admissibility of
[def-trf-admissibility], so that $R\Gamma_c(C,Rc_1^!K)$ and,
by the identification
$R\Gamma_c(X,Rc_{1!}Rc_1^!K)\cong R\Gamma_c(C,Rc_1^!K)$ of
[def-trf-global-operator] composed with
[def-compact-support-direct-image-detailed],
$R\Gamma_c(X,Rc_{1!}Rc_1^!K)$ are compact-support cohomology of
finite-Tor constructible complexes. Each of these four complexes is
therefore an object of $D^b_{\mathrm{fin}}(A)$, which is the
assertion.
