+++
id = "cor-pod-constant-coefficients"
kind = "theorem"
title = "Constant coefficients"
order = 2443
tags = ["latex:corollary"]
uses = ["def-pod-coefficient-dual-on-x", "def-pod-derived-poincare-pairing", "def-pur-smooth-trace", "def-weil-poincare-trace-cup", "prop-cohomological-finiteness", "prop-pod-cup-product-coherence", "prop-pod-degree-of-the-pairing", "thm-pod-degreewise-perfectness-over-a-field", "thm-pod-derived-poincare-duality", "thm-pod-proper-poincare-duality"]
+++
In the Poincare duality conventions of this chapter (the fixed setting; $X_0$ not necessarily proper), restrict to the field stage $\Lambda\in\{E,\Qlb\}$, and put $K=\Lambda _X$ (perfect, with canonical evaluation the unit identification). Poincare duality is the perfect pairing

$$
H_c^i(X,\Lambda )\times H^{2d-i}\bigl(X,\Lambda (d)\bigr) \longrightarrow \Lambda ,
$$

equivalently the line-valued pairing

$$
H_c^i(X,\Lambda )\times H^{2d-i}(X,\Lambda ) \longrightarrow \Lambda (-d),
$$

for every $i\in \mathbf Z$. Since $X$ is geometrically connected, the $i=2d$ case together with $H^0(X,\Lambda)\cong\Lambda$ (the connectedness clause of Proposition 1.58) gives

$$
H_c^{2d}\bigl(X,\Lambda (d)\bigr)\cong \Lambda , \qquad H_c^{2d}(X,\Lambda )\cong \Lambda (-d),
$$

with the first isomorphism induced by the trace map $\operatorname{tr}_X$; if $X_0$ is proper, the same holds with $H_c$ replaced by $H$.

## Proof

Step 1: the coefficient dual of the constant object. For $K=\Lambda _X$, $K^\vee =R\mathcal Hom_X(\Lambda _X,\Lambda _X)=\Lambda _X$ with the unit identification as the canonical evaluation, by the internal-Hom with the unit object of [def-pod-coefficient-dual-on-x]; therefore

$$
K^\vee (d)[2d]=\Lambda _X(d)[2d].
$$

Step 2: the pairings. By [thm-pod-derived-poincare-duality] the derived pairing is perfect, and by [thm-pod-degreewise-perfectness-over-a-field] the degreewise pairings

$$
H_c^i(X,\Lambda )\times H^{2d-i}\bigl(X,\Lambda (d)\bigr)\to \Lambda
$$

are perfect; the line-valued form is the twist elimination of [prop-pod-degree-of-the-pairing]. None of this uses properness. Step 3: the top degree. Perfectness at $i=2d$ gives $H_c^{2d}(X,\Lambda )\cong H^0(X,\Lambda (d))^\vee$. Since $X_0$ is geometrically connected, $X$ is connected and $H^0(X,\Lambda )\cong \Lambda$ with the geometric Frobenius acting as the identity, by the connectedness clause of [prop-cohomological-finiteness], which needs no properness; hence $H^0(X,\Lambda(d))\cong\Lambda(d)$ and $H_c^{2d}(X,\Lambda)\cong\Lambda(d)^\vee=\Lambda(-d)$, and twisting by $d$ ([prop-pod-degree-of-the-pairing]) gives $H_c^{2d}(X,\Lambda (d))\cong \Lambda$. Step 4: the identification with the trace. Under this duality, moved by the twist elimination of [prop-pod-degree-of-the-pairing] to $H_c^{2d}(X,\Lambda(d))\times H^0(X,\Lambda)\to\Lambda$, $x\in H_c^{2d}(X,\Lambda(d))$ corresponds to the functional $1\mapsto\beta(x\otimes 1)$ on $H^0(X,\Lambda)=\Lambda\cdot 1$. By [def-pod-derived-poincare-pairing], $\beta(x\otimes1)$ is the normalized smooth trace of $x\smile_c 1$, and $x\smile_c1=x$ by the unit clause of [prop-pod-cup-product-coherence]; so the isomorphism $H_c^{2d}(X,\Lambda(d))\cong\Lambda$ is $x\mapsto\operatorname{Tr}^{\mathrm{sm}}_{a_X,\Lambda}(x)$, the counit of $Ra_{X!}\dashv Ra_X^!$ through $\eta_X$ with the normalization of [def-pur-smooth-trace], i.e. the trace map $\operatorname{tr}_X$ of [def-weil-poincare-trace-cup] (whose definition on $H_c^{2d}$ uses no properness); its untwisted form is $\operatorname {tr}^{(-d)}_X:H_c^{2d}(X,\Lambda)\to\Lambda(-d)$. The last assertion (for $X_0$ proper, $H_c$ replaced by $H$) is the proper comparison of [thm-pod-proper-poincare-duality].
