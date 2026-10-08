+++
id = "def-weil-finite-tor-amplitude"
kind = "definition"
title = "Finite Tor amplitude"
order = 1464
uses = ["def-weil-algebraically-closed-coefficients", "def-weil-derived-cohomology-sheaves", "def-weil-derived-complete-integral-detailed", "def-weil-derived-tensor", "def-weil-finite-torsion-constructibility", "def-weil-rationalization-karoubi"]
+++
Fix a prime $\ell$, a finite extension $E/\Ql$, an integer $n\in\mathbf
Z_{\geq1}$, and a scheme $Y$ on which $\ell$ is invertible. Put $A=A_{E,n}$
and use the derived cohomology sheaves
[def-weil-derived-cohomology-sheaves] and the derived tensor product
[def-weil-derived-tensor]. For an object $K\in D^b_c(Y,A)$ satisfying the
finite-torsion constructibility condition
[def-weil-finite-torsion-constructibility], say that $K$ has *finite Tor
amplitude* if there are integers $a\leq b$ such that, for every sheaf $M$ of
$A$-modules placed in degree zero,

$$
 \mathcal H^r(K\otimes^L_A M)=0
 \qquad\text{for every }r\in\mathbf Z\setminus[a,b].
$$

Define $D^b_{ctf}(Y,A)$ as the full triangulated subcategory of such objects.
For $K\in D^b_c(Y,\mathcal O_E)$, a derived-complete bounded constructible
complex [def-weil-derived-complete-integral-detailed], say that $K$ has
finite Tor amplitude if every reduction $K\otimes^L_{\mathcal O_E}A_{E,j}$,
$j\in\mathbf Z_{\geq1}$, has finite Tor amplitude with one interval
independent of $j$, and define $D^b_{ctf}(Y,\mathcal O_E)$ accordingly. At
field coefficients the finite-Tor subcategories are, by definition, the
bounded constructible rationalized category
[def-weil-rationalization-karoubi] and its common-stage algebraically closed
coefficient category [def-weil-algebraically-closed-coefficients]:

$$
 D^b_{ctf}(Y,E):=D^b_c(Y,E),
 \qquad
 D^b_{ctf}(Y,\Qlb):=D^b_c(Y,\Qlb).
$$

The second equality is interpreted in the finite-stage triangulated
2-colimit. For $A_{E,n}$, finite Tor amplitude is an additional condition and
does not follow from bounded constructibility. At the integral stage it is
imposed by the displayed definition; the separate residue-field argument
below proves that every object of the derived-complete constructible category
in fact satisfies it. This conclusion uses the compatibility of all
reductions of one integral object.
