+++
id = "d-curve-pieces"
kind = "definition"
title = "Curve coefficient pieces"
order = 2340
uses = ["def-trf-coefficient-conventions", "def-trf-coefficient-pushforward", "def-trf-frobenius-coefficient-morphism", "def-trf-frobenius-operators", "def-trf-graph-correspondence", "def-trf-iterated-weil-map", "def-trf-scheme-frobenius", "prop-functor-package", "prop-sf-open-closed-triangle-all-stages"]
+++
Fix the coefficient conventions of [def-trf-coefficient-conventions] and a
Weil complex $(K,\varphi)$ on $X=X_0\times_{k_0}k$, where $X_0$ is smooth of
pure dimension one. Fix $m\ge1$ and $x\in X_0(\mathbf F_{q^m})$, and on $X$
let $i:\{\bar x\}\hookrightarrow X$ and $j:U=X\setminus\{\bar x\}\hookrightarrow X$.
The *curve pieces* of $K$ at $x$ are

$$
K^Z=Ri_*i^*K,\qquad K^U=j_!j^*K,
$$

the outer terms of the open–closed triangle
$K^U\to K\to K^Z\xrightarrow{+1}$ of [prop-sf-open-closed-triangle-all-stages].
Let $\Phi_m$ be the $m$-th power of the Frobenius of
[def-trf-scheme-frobenius], $\varphi_m$ the iterated Weil map of
[def-trf-iterated-weil-map] (the scheme-Frobenius map
$u_m:\Phi_m^*K\to K$), and $F_{x,m}$ the stalk Frobenius at $\bar x$
of [def-trf-frobenius-operators], which is the stalk map of $\varphi_m$
at the fixed point $\bar x$. The morphism $\Phi_m$ is finite and a
universal homeomorphism fixing $\bar x$, so $\Phi_m^{-1}(U)=U$, the
square of $j$ over $\Phi_m$ is Cartesian with restriction
$\Phi_{m,U}:U\to U$, and $\Phi_mi=i$. The induced maps on the two
pieces are:

- on the graph correspondence $(1,\Phi_m)$ of [def-trf-graph-correspondence],
  $u^Z=[i,i]_!(F_{x,m})$, the proper pushforward of
  [def-trf-coefficient-pushforward] of the stalk map, along the proper
  pushforward diagram $(i,i)$ from the point correspondence
  $(\operatorname{id},\operatorname{id})$ on $\{\bar x\}$ with coefficient
  $F_{x,m}$ on $K_{\bar x}$ to the graph $(1,\Phi_m)$ (a diagram because
  $1\circ i=i\circ\operatorname{id}$ and $\Phi_mi=i\circ\operatorname{id}$).
  Both exceptional legs being identities, the exceptional half of
  [def-trf-coefficient-pushforward] is the identity, and
  $u^Z=Ri_*F_{x,m}\circ\gamma$, where
  $\gamma:\Phi_m^*Ri_*i^*K\to Ri_*i^*K$ is the ordinary half, the
  composite of the unit of $i^*\dashv Ri_*$ with $Ri_*$ of the counit,
  through $i^*\Phi_m^*=(\Phi_mi)^*=i^*$;
- $u^U$, the composite

$$
\Phi_m^*j_!j^*K\simeq j_!\Phi_{m,U}^*j^*K
\xrightarrow{j_!j^*\varphi_m}j_!j^*K,
$$

  whose first isomorphism is open $!$-base change for the Cartesian
  square of $j$ over $\Phi_m$ ([prop-functor-package], clause (4)).

The same construction applies verbatim when $\varphi_m$ is replaced by a
Frobenius coefficient morphism $v:\Phi_m^*K\to K$ in the sense of
[def-trf-frobenius-coefficient-morphism] (no Weil structure and no
invertibility), with $F_{x,m}$ replaced by the stalk map
$v_{\bar x}:K_{\bar x}\cong(\Phi_m^*K)_{\bar x}\to K_{\bar x}$. It
uses neither smoothness nor dimension one: it applies verbatim to any
separated finite-type $X_0$, and the smooth-curve case is the one needed
for the trace formula.
