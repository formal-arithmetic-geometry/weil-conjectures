+++
id = "thm-pod-point-perfectness"
kind = "theorem"
title = "Point perfectness of global sections"
order = 2249
uses = ["cor-sf-direct-image-ctf-proetale", "def-coef-normalized-dvr-tower", "def-compact-support-direct-image-detailed", "def-pod-conventions", "def-pod-perfect-point-complex", "def-weil-algebraically-closed-coefficients", "def-weil-derived-complete-integral-detailed", "def-weil-derived-direct-image", "def-weil-finite-coefficient-point", "def-weil-finite-tor-amplitude", "def-weil-finite-torsion-constructibility", "def-weil-integral-rational-qbar-compact-support", "def-weil-ordinary-compact-cohomology", "def-weil-rationalization-karoubi", "lem-coef-finite-direct-image", "lem-coef-integral-compact-support", "lem-coef-integral-residue-tor", "lem-coef-normalized-dvr-effectivity", "lem-trf-finite-tor-amplitude-perfect", "prop-trf-compact-support-perfectness"]
+++
Fix the finite-field datum and the coefficient stages
$\Lambda\in\{A_{E,n},\mathcal O_E,E,\Qlb\}$ of the Poincare duality
conventions [def-pod-conventions], but let $X_0$ be an arbitrary
separated finite-type $k_0$-scheme: neither properness nor smoothness
of $X_0$ is assumed. Put $X=X_0\times_{k_0}k$, let
$a_X:X\to s=\Spec k$ be the structure morphism, and let
$d\geq\dim X$. Let $K\in D^b_{ctf}(X,\Lambda )$. Then the four
complexes

$$
R\Gamma (X,K),\qquad R\Gamma _c(X,K),\qquad R\Gamma (X,K)^\vee,\qquad R\Gamma _c(X,K)^\vee
$$

are perfect point complexes at every coefficient stage, in the
following sense.

1. At finite level $\Lambda=A=A_{E,n}$ they are bounded with finite
cohomology modules and finite Tor amplitude, i.e. quasi-isomorphic to
bounded complexes of finite free $A$-modules
([def-pod-perfect-point-complex]). If $K$ has Tor amplitude in
$[a,b]$, then $R\Gamma(X,K)$ and $R\Gamma_c(X,K)$ have Tor amplitude
in $[a,b+2d]$ and their duals in $[-b-2d,-a]$.
1. At the stage $\mathcal O_E$ they lie in
$D^b_{\mathrm{fg}}(\mathcal O_E)$ and are perfect; their reductions
modulo $\varpi_E^n$ are the corresponding finite-level complexes of the
reductions $K_n=K\otimes^L_{\mathcal O_E}A_{E,n}$, and these are
perfect with one common amplitude independent of $n$.
1. At the stages $E$ and $\Qlb$ they are bounded with
finite-dimensional cohomology.

If $X_0$ is proper, the canonical comparison
$R\Gamma_c(X,K)\xrightarrow{\sim}R\Gamma(X,K)$ of
[def-weil-ordinary-compact-cohomology] identifies the two cases; in
particular this applies in the fixed setting of
[def-pod-conventions]. (Source: the finiteness theorems of etale
cohomology, Milne, Lectures on Etale Cohomology, Sections 19 and 29,
for the finiteness and the perfectness at the point. The finite-level
compact-support membership $R\Gamma _c(X,K)\in D^b_{\mathrm{fin}}(A)$
is recorded in [prop-trf-compact-support-perfectness].)

## Proof

*Step 1: the finite level.* Let $\Lambda=A=A_{E,n}$ and let
$K\in D^b_{ctf}(X,A)$ have Tor amplitude in $[a,b]$
([def-weil-finite-torsion-constructibility],
[def-weil-finite-tor-amplitude]). At the geometric point $s$ a bounded
constructible complex is a bounded complex of $A$-modules with finite
cohomology ([def-weil-finite-coefficient-point]), and the Tor
amplitude of a complex on $s$ is the Tor amplitude of the underlying
$A$-module complex, since the sheaves of $A$-modules on $s$ are the
$A$-modules.

For ordinary cohomology, apply [cor-sf-direct-image-ctf-proetale]
to the separated finite-type morphism $a_X:X\to s$: the complex
$Ra_{X,*}K$ is bounded constructible with Tor amplitude in
$[a,b+2d]$. Hence $R\Gamma(X,K)$ is bounded, has finite cohomology
modules, and has Tor amplitude in $[a,b+2d]$. No properness is used.

For compact support, choose a compactification $a_X=\bar a\circ j$
with $j:X\hookrightarrow\bar X$ an open immersion and $\bar a$ proper
([def-compact-support-direct-image-detailed]); replacing $\bar X$ by
the scheme-theoretic closure of $X$ we may assume $\dim\bar X\leq d$.
Then $Ra_{X,!}K=R\bar a_*j_!K$. Extension by zero is exact and
commutes with derived tensor product, as one checks on stalks, so
$j_!K$ is bounded constructible with Tor amplitude in $[a,b]$, and
[cor-sf-direct-image-ctf-proetale] applied to $\bar a$ gives Tor
amplitude in $[a,b+2d]$ for $R\Gamma_c(X,K)$. The finiteness and
boundedness of its cohomology is
[prop-trf-compact-support-perfectness].

By [lem-trf-finite-tor-amplitude-perfect], a bounded complex of
$A$-modules with finite cohomology and Tor amplitude in $[a',b']$ is
quasi-isomorphic to a complex $P^\bullet$ of finite free $A$-modules
with $P^i=0$ for $i\notin[a',b']$. Hence $R\Gamma(X,K)$ and
$R\Gamma_c(X,K)$ are represented by bounded complexes of finite free
$A$-modules in degrees $[a,b+2d]$. For such a $P^\bullet$ the derived
dual $P^{\bullet\vee}=R\operatorname{Hom}_A(P^\bullet,A)$ is computed
termwise, $P^\bullet$ being a bounded complex of projectives, and is
the complex of finite free modules $\operatorname{Hom}_A(P^{-i},A)$
in degrees $[-b-2d,-a]$. Thus all four complexes are perfect point
complexes in the sense of [def-pod-perfect-point-complex], with the
stated amplitudes.

*Step 2: the stage $\mathcal O_E$.* Put $R=\mathcal O_E$,
$A_n=A_{E,n}$, $\kappa=A_1$, and let $K\in D^b_c(X,R)$ be a
derived-complete integral object
([def-weil-derived-complete-integral-detailed]) with reductions
$K_n=K\otimes^L_RA_n$. By [lem-coef-integral-residue-tor] all the
$K_n$ have Tor amplitude in one interval $[a,b]$, namely the
cohomological range of $K_1$. By Step 1 every
$R\Gamma(X,K_n)$ and $R\Gamma_c(X,K_n)$ is a bounded complex of finite
free $A_n$-modules in the common interval $[a',b']=[a,b+2d]$.

For compact support, [lem-coef-integral-compact-support] applied to
$a_X$ gives $R\Gamma_c(X,K)\in D^b_c(s,R)$ with
$R\Gamma_c(X,K)\otimes^L_RA_n\cong R\Gamma_c(X,K_n)$, these
reductions having the uniform Tor interval $[a,b+2d]$; the integral
compact support is the one of
[def-weil-integral-rational-qbar-compact-support].

For ordinary cohomology, by [def-weil-derived-direct-image]
$R\Gamma(X,K)=R\varprojlim_nR\Gamma(X,K_n)$. The coefficient
comparisons of [lem-coef-finite-direct-image], applied to the
quotients $A_m\to A_n$ ($m\geq n$), are isomorphisms
$R\Gamma(X,K_m)\otimes^L_{A_m}A_n\xrightarrow{\sim}R\Gamma(X,K_n)$
compatible with successive quotients, so
$(R\Gamma(X,K_n))_n$ is a normalized DVR tower on the point
([def-coef-normalized-dvr-tower]).
[lem-coef-normalized-dvr-effectivity] then gives
$R\Gamma(X,K)\otimes^L_RA_n\cong R\Gamma(X,K_n)$ for all $n$, and
$R\Gamma(X,K)$ is derived complete.

It remains to see that a derived-complete $R$-complex $C$ whose
reductions $C_n=C\otimes^L_RA_n$ are perfect with amplitude in
$[a',b']$ is perfect. The triangle
$C\xrightarrow{\varpi_E}C\to C_1\to$ gives exact sequences

$$
0\to H^i(C)/\varpi_EH^i(C)\to H^i(C_1)\to H^{i+1}(C)[\varpi_E]\to0 .
$$

Each $H^i(C)$ is a derived-complete $R$-module, the cohomology modules
of a derived-complete complex being derived complete. By the derived
Nakayama lemma for the ideal $(\varpi_E)$ of the Noetherian ring $R$,
a derived-complete module $M$ with $M/\varpi_EM=0$ vanishes, and one
with $M/\varpi_EM$ finitely generated is finitely generated. Hence
$H^i(C)=0$ for $i\notin[a',b']$ and every $H^i(C)$ is a finitely
generated $R$-module, i.e. $C\in D^b_{\mathrm{fg}}(R)$. Since $R$ is
a discrete valuation ring, every finitely generated $R$-module has a
two-term resolution by finite free modules and every complex over $R$
is quasi-isomorphic to the sum of its shifted cohomology modules;
therefore $C$ is quasi-isomorphic to a bounded complex of finite free
$R$-modules, i.e. it is perfect ([def-pod-perfect-point-complex]),
and its reductions are the perfect complexes $C_n$ of common
amplitude $[a',b']$. Applied to $C=R\Gamma(X,K)$ and
$C=R\Gamma_c(X,K)$ this proves the assertion for these two complexes.

For the duals, if $P^\bullet$ is a bounded complex of finite free
$R$-modules representing $C$, then $C^\vee$ is the termwise dual
complex, again bounded and finite free, and
$C^\vee\otimes^L_RA_n\cong\operatorname{Hom}_{A_n}(P^\bullet\otimes_RA_n,A_n)=C_n^\vee$;
by Step 1 these reductions are perfect in the common interval
$[-b',-a']$.

*Step 3: the field stages.* For $\Lambda=E$, the object is the
rationalization of an integral object $K_R$
([def-weil-rationalization-karoubi]), possibly up to a direct
summand, and the operations $R\Gamma$ and $R\Gamma_c$ at the stage $E$
are the rationalizations of the integral ones
([def-weil-derived-direct-image],
[def-weil-integral-rational-qbar-compact-support]). By Step 2 they
are $C\otimes_RE$ with $C$ a perfect $R$-complex; since
$R\to E$ is flat, $H^i(C\otimes_RE)=H^i(C)\otimes_RE$ is
finite-dimensional and vanishes outside the bounded interval of $C$,
and $(C\otimes_RE)^\vee=C^\vee\otimes_RE$ has the same property. A
direct summand of a bounded complex with finite-dimensional cohomology
is again one. For $\Lambda=\Qlb$, the object is represented at a
finite stage $E'/\Ql$ ([def-weil-algebraically-closed-coefficients]),
and all four complexes are obtained from the $E'$-stage complexes by
the exact extension of scalars $-\otimes_{E'}\Qlb$, which preserves
boundedness, finite-dimensionality and commutes with the dual of a
complex with finite-dimensional total cohomology. This proves the
field-stage assertions.

*Step 4: the proper case.* If $X_0$ is proper, then $a_X$ is proper
and the comparison $R\Gamma_c(X,K)\to R\Gamma(X,K)$ of
[def-weil-ordinary-compact-cohomology] is an isomorphism at each
stage, compatible with the constructions above; in the setting of
[def-pod-conventions] this applies when $X_0$ is in addition proper.
