+++
id = "def-coefficient-twists-detailed"
kind = "definition"
title = "Coefficient Tate twists"
order = 1505
uses = ["def-weil-derived-complete-integral-detailed", "def-weil-derived-tensor", "def-weil-finite-tor-amplitude", "def-weil-finite-torsion-constructibility", "def-weil-pbc-proetale-site"]
+++
Fix a prime $\ell$, a finite extension $E/\Ql$, an integer $n\in\mathbf
Z_{\geq1}$, and a scheme $S$ on which $\ell$ is invertible. Use the small
pro-etale site [def-weil-pbc-proetale-site] of $S$ and the derived
tensor product [def-weil-derived-tensor]. For every integer $r\geq1$, define
the pro-etale sheaf $\mu_{\ell^r,S}$ by

$$
 \mu_{\ell^r,S}(U)=
 \{u\in\Gamma(U,\mathcal O_U^\times):u^{\ell^r}=1\}
 \qquad(U\to S).
$$

With transition maps $u\mapsto u^\ell$, use the finite-torsion coefficient
[def-weil-finite-torsion-constructibility] $A_{E,n}$ from the global
coefficient notation, and define

$$
  \Zl(1)_S=\varprojlim_{r\geq1}\mu_{\ell^r,S},\qquad
  \mathcal O_E(1)_S=\Zl(1)_S\otimes_{\Zl}\mathcal O_E,
$$

and

$$
  A_{E,n}(1)_S=
  \mathcal O_E(1)_S\otimes_{\mathcal O_E}A_{E,n},
 \qquad E(1)_S=\mathcal O_E(1)_S\otimes_{\mathcal O_E}E.
$$

The $\Qlb$-twist is represented by $E(1)_S$ at every finite stage and is
compatible with scalar extension. For each displayed coefficient ring
$\Lambda\in\{A_{E,n},\mathcal O_E,E,\Qlb\}$, let $\Lambda_S$ denote its
coefficient object on $S$: it is the finite-level constant sheaf
$(A_{E,n})_S$ for $\Lambda=A_{E,n}$, the completed coefficient sheaf
$\widehat{\mathcal O}_{E,S}$ from the derived-complete integral construction
[def-weil-derived-complete-integral-detailed] for $\Lambda=\mathcal O_E$, and
the scalar extensions of these objects for $\Lambda=E,\Qlb$, with $\Qlb$
interpreted at a common finite stage. Thus, for each coefficient ring,
$\Lambda(1)_S$ is respectively the finite-level object $A_{E,n}(1)_S$, the
integral object $\mathcal O_E(1)_S$, the rational object $E(1)_S$, or its
common-stage $\Qlb$-extension. Define the twist for every $m\in\mathbf Z$ by

$$
 \Lambda(m):=
 \begin{cases}
   \Lambda_S,&m=0,\\
   \Lambda(1)_S^{\otimes_{\Lambda_S}m},&m>0,\\
   \operatorname{Hom}_{\Lambda_S}\bigl(\Lambda(-m),\Lambda_S\bigr),&m<0.
 \end{cases}
$$

For every $m\in\mathbf Z$ and every $K\in D(S_{\mathrm{proet}},\Lambda)$, set

$$
 K(m)=K\otimes^L_{\Lambda_S}\Lambda(m).
$$
