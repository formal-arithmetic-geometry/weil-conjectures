+++
id = "def-sf-categories"
kind = "remark"
title = "Ambient categories and small subcategories"
order = 2041
+++
Fix a scheme $T$ carrying a coefficient stage $\Lambda$ and a site — the
*small étale* or the *small pro-étale* site of
def:weil-pbc-etale-site and def:weil-pbc-proetale-site. The
*ambient* categories are the ordinary derived categories of
$\Lambda_T$-modules

$$
D(T,\Lambda),\quad D^+(T,\Lambda),\quad D^-(T,\Lambda),\quad D^b(T,\Lambda),
$$

together with, for a set of primes $P$ invertible on $T$, the full
subcategory $D^+_{P\text{-tor}}(T,\Lambda)$ of complexes whose geometric
stalks are torsion with prime divisors in $P$
(sbc-def-derived-categories-with-allowable-torsion). The *small*
categories are the full subcategories

$$
\Dbc(T,\Lambda)\subseteq D^b(T,\Lambda),\qquad
\Dctf(T,\Lambda)\subseteq\Dbc(T,\Lambda),\qquad
D_c^{[a,b]}(T,\Lambda)\subseteq\Dbc(T,\Lambda)
$$

of bounded constructible complexes, of bounded constructible complexes of
finite Tor amplitude, and of bounded constructible complexes with cohomology
concentrated in $[a,b]$
(def:weil-finite-torsion-constructibility,
def:weil-finite-tor-amplitude,
def:weil-constructible-intervals); at the field stages
$\Dctf=\Dbc$ by definition.
