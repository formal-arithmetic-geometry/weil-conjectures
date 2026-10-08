+++
id = "lem-pur-ordinary-kunneth-finite-ring"
kind = "lemma"
title = "Ordinary Kunneth at a finite coefficient ring"
order = 1937
uses = ["def-kun-derived-tensor", "def-kun-kunneth-map", "def-weil-finite-field-fiber", "def-weil-pbc-derived-categories", "def-weil-scheme-morphism-properties", "lem-kun-0f10", "lem-kun-0f12", "thm-kun-0f1p"]
+++
Let $k$ be the algebraically closed field of
[def-weil-finite-field-fiber], and let $X,Y$ be
separated finite-type
$k$-schemes. Put $A=\mathcal O_E/\varpi_E^n$, for $E/\mathbf Q_\ell$ finite, $n\geq1$, and $\ell\neq\operatorname{char}(k)$.
For $K\in D(X_{\mathrm{et}},A)$ and
$L\in D(Y_{\mathrm{et}},A)$ in the
derived categories,
write $K\boxtimes_A^L L=p_X^*K\otimes_A^Lp_Y^*L$, using the
derived tensor product.
The exterior-product map is an isomorphism

$$
R\Gamma(X,K)\otimes_A^LR\Gamma(Y,L)
\longrightarrow R\Gamma(X\times_kY,K\boxtimes_A^L L).
$$

## Proof

First consider a finite residue field $\kappa$ of characteristic
$\ell$. Forget to $\mathbf F_\ell$-coefficients and apply
[thm-kun-0f1p] with $n=\ell$.
The resulting Kunneth map has a natural action of
$\kappa\otimes_{\mathbf F_\ell}\kappa$.
Since finite fields are separable, there is a central idempotent
$e$ in this algebra with
$e(\kappa\otimes_{\mathbf F_\ell}\kappa)\cong\kappa$, the factor
on which the two $\kappa$-actions agree.
For example, writing $\kappa=\mathbf F_\ell[\theta]$ with
separable minimal polynomial $g$, the decomposition of
$\kappa[t]/(g)$ into the $t-\theta$ factor and its coprime
complement gives $e$ by the Chinese remainder theorem.
For any two complexes of $\kappa$-vector spaces or sheaves,

$$
e(P\otimes_{\mathbf F_\ell}^L Q)\cong P\otimes_\kappa^L Q.
$$

This follows termwise for vector spaces and then for K-flat
representatives of the tensor product in
[def-kun-derived-tensor].
The same direct-summand operation commutes with derived sections.
Applying $e$ to the $\mathbf F_\ell$-isomorphism proves the
$\kappa$-coefficient assertion, for arbitrary complexes.

Now let $\kappa=A/(\varpi_E)$.
All three schemes have finite cohomological dimension by
[lem-kun-0f10]. The constant-tensor comparison
[lem-kun-0f12], applied with the $A$-module $\kappa$,
gives

$$
R\Gamma(T,H)\otimes_A^L\kappa
\cong R\Gamma(T,H\otimes_A^L\underline\kappa)
\qquad(T=X,Y,X\times_kY).
$$

These comparisons identify the reduction of the $A$-Kunneth map
with the $\kappa$-Kunneth map for
$K\otimes_A^L\kappa,L\otimes_A^L\kappa$: both maps are induced by
the tensor product of the two pulled-back counits in
[def-kun-kunneth-map], and derived scalar extension commutes
with that tensor product. These reductions need not be bounded;
the preceding field-coefficient result permits arbitrary complexes.

Let $D$ be the cone of the $A$-Kunneth map.
We have proved $D\otimes_A^L\kappa=0$.
The finite filtration
$A\supset\varpi_EA\supset\cdots\supset\varpi_E^nA=0$
has quotients finite-dimensional over $\kappa$.
By derived tensor associativity,
$D\otimes_A^L Q=0$ for every such quotient $Q$.
Tensor the short exact sequences of this filtration with $D$
and use their distinguished triangles, starting at the zero term.
Induction gives $D\otimes_A^L A=0$, hence $D=0$.
This proves the stated isomorphism and its naturality.
