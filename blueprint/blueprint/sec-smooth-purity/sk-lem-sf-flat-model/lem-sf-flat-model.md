+++
id = "lem-sf-flat-model"
kind = "lemma"
title = "Bounded flat model of finite Tor amplitude"
order = 1831
uses = ["def-weil-derived-tensor", "def-weil-finite-tor-amplitude", "def-weil-finite-torsion-constructibility", "def-weil-pbc-proetale-site", "lem-exc-constant-inverse-image-flat"]
+++
Fix the global finite-field datum, a prime $\ell\ne p$, an integer
$n\in\mathbf Z_{\geq1}$, and put $A=A_{E,n}$. Let $T$ be a scheme on
which $\ell$ is invertible, and let $K\in D^b_c(T,A)$ be a
bounded constructible
complex of $A_T$-modules on the
small pro-étale site. For
integers $a\leq b$ the following two conditions are equivalent.

1. **(i)** $K$ has finite Tor
amplitude in $[a,b]$: for every sheaf $M$ of $A_T$-modules placed in
degree zero one has $\mathcal H^r(K\otimes_A^LM)=0$ for every
$r\in\mathbf Z\setminus[a,b]$.
1. **(ii)** $K$ is isomorphic in $D(T_{\mathrm{proet}},A)$ to a bounded
complex $P$ of *flat* $A_T$-module sheaves with $P^q=0$ for
$q\notin[a,b]$, flatness meaning, as in
[lem-exc-constant-inverse-image-flat], that $P^q\otimes_A-$
preserves injections of $A_T$-module sheaves.

The same equivalence holds with the corresponding constructibility,
derived-tensor and Tor-amplitude conditions on a small étale site.

*Constructible variant.* If $T$ is Noetherian (for instance of finite type
over $k$) and $K\in D^b_c(T_{\Et},A)$ on the small étale site has finite Tor
amplitude in $[a,b]$, then $K$ is isomorphic in $D(T_{\Et},A)$ to a bounded
complex $P$ of flat *constructible* $A_T$-module sheaves with $P^q=0$ for
$q\notin[a,b]$; in particular every object of $D^b_{ctf}(T_{\Et},A)$ has such
a model. The key input is that every constructible sheaf of $A$-modules on
$T_{\Et}$ is a quotient of a finite direct sum of sheaves $j_{V!}A_V$ with
$j_V:V\to T$ étale and $V$ affine (Stacks 095M; SGA $4\frac12$, Rapport, 4.6),
and that kernels and cokernels of maps of constructible sheaves of
$A$-modules are constructible.

## Proof

*(ii)$\Rightarrow$(i).* A bounded-above complex of flat module
sheaves is K-flat: if $Q$ is acyclic
then each $P^q\otimes_AQ$ is acyclic, because $P^q\otimes_A-$ is exact
by flatness, and the total complex of a double complex one of whose
directions is acyclic is acyclic. Hence $K\otimes_A^LM\cong P\otimes_AM$
by [def-weil-derived-tensor]; the complex $P\otimes_AM$ has terms
only in degrees $[a,b]$, each $P^q\otimes_AM$ being concentrated in
degree $q$ again by exactness of $P^q\otimes_A-$, and therefore
$\mathcal H^r(K\otimes_A^LM)=0$ for $r\notin[a,b]$, which is (i).

*(i)$\Rightarrow$(ii).* Assume (i) and choose a bounded-above
resolution $P\to K$ by free $A_T$-module sheaves with $P^q=0$ for
$q>b$: in decreasing degree one covers the cycles at hand by the free
module sheaf on the sections of a set of objects of the site, which is the
usual degreewise free resolution of a complex and stabilizes in each fixed
degree. Free sheaves are flat, so $P$ is a bounded-above complex of flat
sheaves, hence K-flat as above, and $K\otimes_A^LM\cong P\otimes_AM$ for
every complex $M$ by [def-weil-derived-tensor]. Testing with the
coefficient sheaf $M=A_T$ gives $\mathcal H^q(P)=\mathcal H^q(K)=0$ for
$q<a$. Put $Q=P^a/\operatorname{im}(P^{a-1}\to P^a)$. Since $P$ is
exact in degrees below $a$, the complex

$$
\cdots\longrightarrow P^{a-1}\longrightarrow P^a
\longrightarrow Q\longrightarrow0
$$

is a flat resolution of $Q$, so for every sheaf $M$ of $A_T$-modules
the module $\operatorname{Tor}^A_1(Q,M)$ is the homology in degree
$a-1$ of this complex tensored with $M$, that is,

$$
\operatorname{Tor}^A_1(Q,M)
=\mathcal H^{a-1}(P\otimes_AM)
=\mathcal H^{a-1}(K\otimes_A^LM)=0,
$$

the last equality because $a-1\notin[a,b]$ and (i), and the first because
the terms of $P$ in degrees above $a$ do not contribute to the homology
in degree $a-1$. Vanishing of $\operatorname{Tor}^A_1(Q,-)$ on all
module sheaves means that $Q$ is flat: this is the Tor form of the
finite-relation criterion for flatness recalled in the proof of
[lem-exc-constant-inverse-image-flat]. The complex

$$
P'=\bigl[Q\to P^{a+1}\to\cdots\to P^b\bigr],
$$

with $Q$ in degree $a$, is then a bounded complex of flat sheaves
concentrated in degrees $[a,b]$, and the canonical map $P'\to K$ is a
quasi-isomorphism: the truncation $\sigma_{\geq a}P$, whose terms are
those of $P'$ with the induced differentials, maps quasi-isomorphically
to $P$ because $P$ is exact below $a$, and $P\to K$ is a
quasi-isomorphism by construction. This is (ii).

*Constructible variant.* Run (i)$\Rightarrow$(ii) on $T_{\Et}$ with a
bounded-above resolution $P\to K$, $P^q=0$ for $q>b$, whose terms are finite
direct sums of sheaves $j_{V!}A_V$, $V\to T$ affine étale. Such a resolution
is built inductively in decreasing degree: at each step one needs a map from
a finite direct sum of sheaves $j_{V!}A_V$ onto a constructible sheaf (first
the cohomology sheaves of $K$, then the kernels and cokernels that arise, all
constructible because the cohomology sheaves of $K$ are and the constructible
sheaves of $A$-modules form an abelian subcategory), and such a surjection
exists by the key input; where the map has to be lifted through a surjection
of sheaves, one refines each $V$ by a finite affine étale cover, over which
the relevant sections lift, and the composite stays surjective
(SGA $4\frac12$, Rapport, 4.6–4.8). The terms of $P$ are flat and
constructible, so the argument above applies verbatim, and
$Q=P^a/\operatorname{im}(P^{a-1}\to P^a)$ is the cokernel of a map of
constructible sheaves, hence constructible as well as flat. Thus
$P'=[Q\to P^{a+1}\to\cdots\to P^b]$ is a bounded complex of flat
constructible sheaves in degrees $[a,b]$, quasi-isomorphic to $K$.
