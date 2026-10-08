+++
id = "thm-pod-trace-isomorphism"
kind = "theorem"
title = "Trace isomorphism"
order = 2444
uses = ["cor-cbc-proper-coincidence", "cor-pod-constant-coefficients", "cor-pur-finite-stage-smooth-dualizing-complex", "def-pod-trace-cup-reading", "def-pur-smooth-trace", "def-weil-frobenius-coefficient-twists", "def-weil-poincare-trace-cup", "prop-cohomological-finiteness", "thm-pod-proper-poincare-duality"]
+++
In the Poincare duality conventions of this chapter (the fixed setting; $X_0$ not necessarily proper), let the field stage be $\Lambda \in \{ E,\overline{\mathbf Q}_{\ell }\}$ of the datum, and let $\Lambda _X$ be the constant sheaf with its canonical strict Weil structure. The trace map $\operatorname {tr}_X$ of [def-weil-poincare-trace-cup], in the reading of [def-pod-trace-cup-reading], is the counit of $Ra_{X!}\dashv Ra_X^!$ read through the canonical orientation $\eta _X$ of [cor-pur-finite-stage-smooth-dualizing-complex] (the normalized smooth trace), and

$$
\operatorname {tr}_X:\   H_c^{2d}\bigl(X,\Lambda (d)\bigr)\xrightarrow {\  \sim \  }\Lambda
$$

is an isomorphism, and so is its untwisted form (the twist elimination of Definition 1.49)

$$
\operatorname {tr}^{(-d)}_X:\   H_c^{2d}(X,\Lambda )\xrightarrow {\  \sim \  }\Lambda (-d).
$$

For the constant sheaf on the geometrically connected $X$, the geometric Frobenius $F$ acts as the identity on $H^0(X,\Lambda )\cong \Lambda$ and by $q^d$ on $H_c^{2d}(X,\Lambda )\cong \Lambda (-d)$. If $X_0$ is proper, then $H_c^{2d}=H^{2d}$ and $\operatorname {tr}^{(-d)}_X:H^{2d}(X,\Lambda )\xrightarrow{\sim}\Lambda (-d)$ is an isomorphism, with $F$ acting by $q^d$ on $H^{2d}(X,\Lambda)$.

## Proof

By [cor-pod-constant-coefficients] (at $i=2d$, valid without properness), the pairing $H_c^{2d}(X,\Lambda(d))\times H^0(X,\Lambda)\to\Lambda$ is perfect and $H_c^{2d}(X,\Lambda (d))\cong H^0(X,\Lambda )^\vee \cong \Lambda$, the isomorphism being the map induced by the trace, i.e. the $\eta _X$-counit composite with the normalization of [def-pur-smooth-trace], which is $\operatorname {tr}_X$ of [def-weil-poincare-trace-cup]; its untwisting is $\operatorname {tr}^{(-d)}_X:H_c^{2d}(X,\Lambda)\to\Lambda(-d)$. For the Frobenius action, $H^0(X,\Lambda )\cong \Lambda$ with $F$ acting as the identity is the connectedness clause of [prop-cohomological-finiteness] (no properness needed); for the top degree, the $F$-action on $\Lambda _X(d)$ in the trace is the twist normalization $q^{-d}$, of [def-weil-frobenius-coefficient-twists], so the untwisted form $\Lambda (-d)$ carries the $q^d$-action, again by [def-weil-frobenius-coefficient-twists]. If $X_0$ is proper, $a_X$ is proper and [cor-cbc-proper-coincidence] identifies $Ra_{X!}$ with $Ra_{X*}$ Frobenius-compatibly, so $H_c^{2d}(X,\Lambda)=H^{2d}(X,\Lambda)$ (the proper comparison of [thm-pod-proper-poincare-duality]) and $\operatorname{tr}^{(-d)}_X$ becomes the map $H^{2d}(X,\Lambda)\to\Lambda(-d)$ of [def-weil-poincare-trace-cup], still an isomorphism with $F$ acting by $q^d$.
