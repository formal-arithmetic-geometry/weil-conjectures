+++
id = "lem-exc-comparison-tor-interval"
kind = "lemma"
title = "Site comparison preserves and detects Tor intervals"
order = 2193
uses = ["def-weil-derived-tensor", "def-weil-finite-tor-amplitude", "def-weil-pbc-derived-categories", "def-weil-pbc-site-comparison-morphism", "lem-exc-constant-inverse-image-flat", "prop-weil-pbc-site-comparison-finite-level", "thm-weil-pbc-site-comparison"]
+++
Let $A$ be finite and let $K\in D^+(T_{\Et},A)$.
For integers $a\leq b$, $K$ has
Tor amplitude
in $[a,b]$ if and only if its
pullback
$\nu_T^*K$ has Tor amplitude in the same interval on
the full pro-etale site. The derived categories are the
ordinary ones of [def-weil-pbc-derived-categories].

## Proof

We record the bounded-flat-model argument. If $K$ has
Tor amplitude $[a,b]$, take a bounded-above flat
resolution $P$ with $P^q=0$ for $q>b$.
Such a resolution is constructed by free module sheaves
on site objects, successively covering cycles and kernels.
It is exact in degrees below $a$. Put
$Q=\operatorname{coker}(P^{a-1}\to P^a)$.
For every module sheaf $N$, the flat resolution ending
in $P^a\to Q$ computes

$$
\operatorname{Tor}_1(Q,N)
=\mathcal H^{a-1}(P\otimes N)=0,
$$

by [def-weil-finite-tor-amplitude]. Hence $Q$
is flat, and $[Q\to P^{a+1}\to\cdots\to P^b]$
is a flat representative of $K$ in precisely this interval.
By [lem-exc-constant-inverse-image-flat], its termwise
pullback is still flat. Exactness in
[prop-weil-pbc-site-comparison-finite-level] makes it
a representative of $\nu_T^*K$. Tensoring this bounded
flat complex with any pro-etale module sheaf gives no
cohomology outside $[a,b]$, proving one implication.

For the converse, testing $\nu_T^*K$ with the coefficient
ring first gives its cohomological bound $[a,b]$.
Exactness of $\nu_T^*$ and the sheaf unit isomorphism
in [prop-weil-pbc-site-comparison-finite-level] make
$\nu_T^*$ conservative on sheaves, hence give the same
cohomological bound for $K$. Take a bounded-above flat
resolution of $K$ and of an arbitrary etale module
sheaf $N$. Their pullbacks remain flat by
[lem-exc-constant-inverse-image-flat].
Exact inverse image commutes with ordinary tensor and
the direct sums in these resolutions, giving

$$
\nu_T^*(K\otimes_A^LN)
=\nu_T^*K\otimes_A^L\nu_T^*N
$$

for the derived tensor in [def-weil-derived-tensor].
The right side has the stipulated Tor bound. Conservativity
on its cohomology sheaves gives that bound on the left
before pullback as well. This applies to every $N$,
proving the converse. The derived comparison used here
is the ordinary one of [thm-weil-pbc-site-comparison].
