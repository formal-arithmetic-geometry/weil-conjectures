+++
id = "lemma-weil-pbc-frobenius-tower-compatibility"
kind = "lemma"
title = "Frobenius compatibility with tower transitions"
order = 1335
uses = ["def-weil-pbc-frobenius-corner-structures", "lemma-weil-pbc-frobenius-level-rectangle", "lemma-weil-pbc-level-map-tower-compatibility"]
+++
For the four transitions $a_{n+1,n},b_{n+1,n},c_{n+1,n},d_{n+1,n}$,

$$
\begin{aligned}
a_{n+1,n}\Theta_{A,n+1}
&=\Theta_{A,n}\Phi_{Y'}(a_{n+1,n}),\\
b_{n+1,n}\Theta_{B,n+1}
&=\Theta_{B,n}\Phi_{Y'}(b_{n+1,n}),\\
c_{n+1,n}\Theta_{C,n+1}
&=\Theta_{C,n}\Phi_{Y'}(c_{n+1,n}),\\
d_{n+1,n}\Theta_{D,n+1}
&=\Theta_{D,n}\Phi_{Y'}(d_{n+1,n}).
\end{aligned}
$$

Hence the four corner Weil structures and all four edges are maps of towers.

## Proof

The equation for $B$ follows by naturality of $\kappa_g$ and $\beta_f$ and
the defining equation
$r_{n+1,n}\vartheta_{n+1}=\vartheta_n\Phi_X(r_{n+1,n})$.
The same argument for $\kappa_{g'}$, $\beta_{f'}$, and
$\vartheta_{E,n}$ proves the equation for $D$. For $A$, combine
$b_{n+1,n}h_{n+1}=h_na_{n+1,n}$ with the transport formula for
$\Theta_A$ and the equation for $B$; cancelling $h_n$ gives the first
displayed equation. The equation for $C$ follows identically from
$d_{n+1,n}h'_{n+1}=h'_nc_{n+1,n}$ and the equation for $D$. The finite Weil
rectangle and the four transition equations now say precisely that every
edge is a morphism of Weil towers.
