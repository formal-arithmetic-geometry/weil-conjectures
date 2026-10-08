+++
id = "lem-wf-rank-one-algebraic-extension"
kind = "lemma"
title = "Arithmetic monodromy after finite geometric image"
order = 2534
uses = ["def-wf-arithmetic-monodromy-extension", "def-wf-geometric-monodromy-group"]
+++
Let $\chi:W(X_0)\to E^\times$ be a continuous rank-one Weil character,
assume that $A=\chi(\Pi)$ is finite, and let $s$ have degree one;
put $c=\chi(s)$. For the rank-one
representation $\rho=\chi$, one has

$$
H_{\mathrm{geom}}(\chi)=A,
\qquad
G_{\mathrm{arith}}(\chi)=A\times\mathbf Z,
\qquad
j_\chi(a,m)=ac^m.
$$

Here $j_\chi:G_{\mathrm{arith}}(\chi)\to\mathbf G_m$ is a regular
homomorphism on every finite-type component.

## Proof

The group $A$ is finite by assumption, hence it is already
Zariski closed in $\mathbf G_m$. Its closure in the sense of
[def-wf-geometric-monodromy-group] is therefore $A$. Conjugation
on $A\subset\mathbf G_m$ is trivial because $\mathbf G_m$ is
abelian, so the multiplication of
[def-wf-arithmetic-monodromy-extension] is direct-product
multiplication. The formula $j_\chi(a,m)=ac^m$ is multiplicative and,
on $A\times\{m\}$, is the regular function $a\mapsto ac^m$.
Finally, $\gamma s^m$ maps to $(\chi(\gamma),m)$, whose image under
$j_\chi$ is $\chi(\gamma)c^m=\chi(\gamma s^m)$.
