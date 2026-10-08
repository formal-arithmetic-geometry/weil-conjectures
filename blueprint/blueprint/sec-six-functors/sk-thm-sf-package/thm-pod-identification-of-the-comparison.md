+++
id = "thm-pod-identification-of-the-comparison"
kind = "theorem"
title = "Identification of the Poincare pairing with Verdier duality"
order = 2253
uses = ["def-exchange-projection", "def-pod-coefficient-dual-on-x", "def-pod-conventions", "def-pod-derived-poincare-pairing", "def-pod-mixed-support-cup-product", "def-pod-perfect-complex-on-x", "def-pod-perfect-derived-pairing", "def-pur-smooth-trace", "def-weil-derived-cohomology-sheaves", "def-weil-derived-direct-image", "def-weil-derived-pullback-tensor-hom", "def-weil-exceptional-inverse-image", "def-weil-finite-coefficient-point", "fix-prop-projection-formula", "lem-sf-tensor-hom", "thm-pod-global-verdier-duality", "thm-pur-finite-coefficient-smooth-purity", "thm-sf-dual-perfect", "thm-sf-identification", "thm-sf-verdier-exchange"]
+++
Fix $\Lambda\in\{A_{E,n},\mathcal O_E,E,\Qlb\}$, the smooth
geometrically connected $k$-scheme $X=X_0\times_{k_0}k$ of dimension $d$
(not necessarily proper), and its
structure morphism $a_X:X\to s=\operatorname{Spec}k$ as in
the Poincare duality conventions.
Let $K\in D^b_{ctf}(X,\Lambda)$ be
perfect over $\Lambda_X$, with
coefficient dual $K^\vee$.
The tensor–internal-Hom adjoint of the
derived Poincare pairing is
the canonical isomorphism

$$
b_K^\sharp:R\Gamma(X,K^\vee(d))[2d]
\xrightarrow{\ \sim\ }R\operatorname{Hom}_\Lambda(R\Gamma_c(X,K),\Lambda).
$$

Its inverse is the global Verdier-duality isomorphism followed by the
smooth-purity identification of the Verdier dual.

## Proof

Work at the chosen coefficient stage. The adjunctions, tensor–Hom
operations and projection transformation below are those at that stage
in [fix-prop-projection-formula] and the adjunction definitions cited below.
They are taken at the chosen coefficient stage.
Put $C=Ra_{X!}K$, $\omega=Ra_X^!\Lambda$, and
$D=Ra_{X*}R\mathcal Hom_X(K,\omega)$. The identification
[thm-sf-dual-perfect] identifies $D$ with the first
object of the displayed map. By
[def-pod-derived-poincare-pairing], [def-pod-coefficient-dual-on-x], [def-pur-smooth-trace],
the pairing, before this identification, is cup product followed by
evaluation into $\omega$ and the counit $Ra_{X!}\omega\to\Lambda$.

Let $T=\Lambda[-r]$ for any integer $r$. This is a perfect point
complex, so its pullback and its tensor product with $K$ are in the
stated finite-Tor domains. The adjunctions and projection
formula give natural bijections

$$
\begin{aligned}
\operatorname{Hom}_s(T,D)
&\cong\operatorname{Hom}_X(La_X^*T,R\mathcal Hom_X(K,\omega))\\
&\cong\operatorname{Hom}_X(K\otimes_\Lambda^LLa_X^*T,Ra_X^!\Lambda)\\
&\cong\operatorname{Hom}_s(Ra_{X!}(K\otimes_\Lambda^LLa_X^*T),\Lambda)\\
&\cong\operatorname{Hom}_s(C\otimes_\Lambda^LT,\Lambda)\\
&\cong\operatorname{Hom}_s(T,R\operatorname{Hom}_\Lambda(C,\Lambda)).
\end{aligned}
$$

Here the first bijection is $La_X^*\dashv Ra_{X*}$ from
[def-weil-derived-direct-image]; the second and fifth are
tensor–internal-Hom adjunction from
[def-weil-derived-pullback-tensor-hom]; the third is
$Ra_{X!}\dashv Ra_X^!$ from
[def-weil-exceptional-inverse-image]; and the fourth is the
projection formula of [def-exchange-projection], [fix-prop-projection-formula].

These bijections are induced by $b_K^\sharp$, not merely abstract
bijections of groups. Indeed, a map $t:T\to D$ is first pulled back
and composed with the counit $La_X^*Ra_{X*}\to\mathrm{id}$, then
evaluated against $K$, then pushed forward and composed with
$Ra_{X!}Ra_X^!\Lambda\to\Lambda$. By
[def-pod-mixed-support-cup-product], this is precisely the map
$C\otimes T\xrightarrow{1\otimes t}C\otimes D\to\Lambda$
obtained from the specified pairing. Its tensor–Hom transpose is
$b_K^\sharp\circ t$. Thus $b_K^\sharp$ induces an isomorphism on
every $H^r=\operatorname{Hom}_s(\Lambda[-r],-)$, under the point-category
equivalences at all four coefficient stages in
[def-weil-finite-coefficient-point]; its cone has zero
cohomology and is zero by [def-weil-derived-cohomology-sheaves].
This proves that the actual adjoint is an isomorphism. The same
adjunction and evaluation characterize the canonical global-duality
comparison of [thm-pod-global-verdier-duality]; consequently the
comparison written there in the reverse direction is its inverse. At every
step the two inputs used are separated: the adjunction, projection and
tensor–internal-Hom calculus is [lem-sf-tensor-hom], [thm-sf-verdier-exchange],
whose abstract outcome is [thm-sf-identification], and the identification
of the Verdier dual of a smooth $X$ with $K^\vee (d)[2d]$ is the
smooth-purity orientation [thm-pur-finite-coefficient-smooth-purity]
consumed through [thm-sf-dual-perfect].
Properness of $X$ is used nowhere in this argument: the adjunctions,
the projection formula and the smooth-purity orientation hold for any
smooth separated finite-type $X$ with admissible $a_X$.
