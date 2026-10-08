+++
id = "thm-pod-qbar-coefficient-pairing"
kind = "theorem"
title = "$\\overline{\\mathbf Q}_{\\ell }$-coefficient pairing"
order = 2451
uses = ["cor-pod-untwisted-similitude", "def-pod-derived-poincare-pairing", "def-weil-algebraically-closed-coefficients", "def-weil-rationalization-karoubi", "prop-weil-pbc-descent-functors", "thm-pod-adic-reconstruction-and-scalar-extension", "thm-pod-degreewise-perfectness-over-a-field", "thm-pod-trace-isomorphism", "thm-pur-rational-and-qbar-purity", "thm-weil-pbc-idempotent-complete-triangulation"]
+++
In the Poincare duality conventions of this chapter (the fixed setting), let $K\in D^b_c(X,\overline{\mathbf Q}_{\ell })$ be perfect over the coefficient sheaf and be represented by an object over some finite $E/\mathbf Q_{\ell }$ as in Definition 1.12. The derived Poincare pairing of Definition 9.17 preserves the corresponding direct summands and is independent of every further finite extension; it defines the perfect derived and degreewise pairings over $\overline{\mathbf Q}_{\ell }$, whose adjoint has inverse the canonical isomorphism

$$
R\Gamma _c(X,K)^\vee \xrightarrow {\  \sim \  } R\Gamma \bigl(X,K^\vee (d)\bigr)[2d]
$$

in the $\overline{\mathbf Q}_{\ell }$-category of Definition 1.13. The degreewise pairings $H_c^i(X,K)\times H^{2d-i}(X,K^\vee(d))\to\overline{\mathbf Q}_{\ell }$ over the field $\overline{\mathbf Q}_{\ell }$ are perfect, the trace $\operatorname {tr}_X:H_c^{2d}(X,\overline{\mathbf Q}_{\ell }(d))\to\overline{\mathbf Q}_{\ell }$ and its untwisted form $\operatorname {tr}^{(-d)}_X:H_c^{2d}(X,\overline{\mathbf Q}_{\ell })\to\overline{\mathbf Q}_{\ell }(-d)$ are isomorphisms (on $H^{2d}$ in place of $H_c^{2d}$ if $X_0$ is proper), and the Frobenius similitude of Corollary 9.31 holds.

## Proof

Represent $K$ by an $E$-object $K_E\in D^b_{ctf}(X,E)$ over the finite $E/\mathbf Q_{\ell }$ stage of the common-stage construction. The $E$-level pairing is perfect by [thm-pod-degreewise-perfectness-over-a-field], and the equivariance by [cor-pod-untwisted-similitude]; the trace isomorphism (in its compact-support form, and on $H^{2d}$ when $X_0$ is proper) is the $E$-level case of [thm-pod-trace-isomorphism]. Finite extension of the coefficient field transports all of it by [thm-pod-adic-reconstruction-and-scalar-extension]; the descent of the pairings to the common-stage category and the independence of the further extensions are the descent functors of [prop-weil-pbc-descent-functors], with the common-stage category of [def-weil-algebraically-closed-coefficients] idempotent complete by the filtered-retract-descent theorem of [thm-weil-pbc-idempotent-complete-triangulation] (so its presentation by an idempotent is unnecessary), and the transport of the duality identification is the corresponding transport of the smooth purity, [thm-pur-rational-and-qbar-purity]. The pairing and its adjoint are thus well defined and perfect; the remaining assertions are the transported degreewise and similitude statements of the $E$-level case.

9.7 The master interface
