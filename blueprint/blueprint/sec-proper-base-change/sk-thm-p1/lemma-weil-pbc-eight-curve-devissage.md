+++
id = "lemma-weil-pbc-eight-curve-devissage"
kind = "lemma"
title = "Short-exact devissage for the eight assertions"
order = 1151
uses = ["def-weil-pbc-eight-curve-assertions", "def-weil-pbc-etale-sheaves"]
+++
Let

$$
0\longrightarrow F_1\xrightarrow{a}F\xrightarrow{b}F_2\longrightarrow0
$$

be exact. If all applicable assertions $\mathcal C_r(X,F_i)$ hold for
$i=1,2$, then all applicable assertions hold for $F$.

## Proof

Pullback to an extension field is exact, so the displayed sequence and its
base change give natural long exact cohomology sequences.

For (1), (2), and (3), in every degree above the stated bound the exact
segment

$$
H^q(X,F_1)\xrightarrow{a_*}H^q(X,F)
\xrightarrow{b_*}H^q(X,F_2)
$$

has zero end terms. Hence its middle term is zero. The hypotheses on
affineness and characteristic are unchanged, and in (3) an extension of two
$p$-power torsion sheaves is again killed by a power of $p$.

For (4) and (5), constructible sheaves form a Serre subcategory: on a common
finite stratification the stalk sequence is an exact sequence of finite
groups. Prime-to-characteristic torsion is also preserved by extensions.
Exactness identifies $H^q(X,F)$ as an extension of
$\operatorname{im}a_*$ by $\operatorname{im}b_*$; these are respectively a
quotient of the finite group $H^q(X,F_1)$ and a subgroup of the finite group
$H^q(X,F_2)$. Thus $H^q(X,F)$ is finite.

For (6) and (7), write the long exact sequence for $F_1,F,F_2$ above its
base-changed sequence. Every square commutes because restriction commutes
with $a$, $b$, and the boundary map obtained from an injective resolution.
For fixed $q$, the four outer vertical arrows in the five-term portion

$$
H^{q-1}(F_2)\to H^q(F_1)\to H^q(F)\to H^q(F_2)\to H^{q+1}(F_1)
$$

are isomorphisms; the five lemma makes the middle arrow an isomorphism.

For (8), let $c\in H^2(W,F|_W)$ and put $c_2=b_*(c)$. Choose
$x_2\in H^2(X,F_2)$ restricting to $c_2$. Its boundary lies in
$H^3(X,F_1)=0$ by (1), so exactness gives
$x\in H^2(X,F)$ with $b_*(x)=x_2$. The difference
$c-x|_W$ maps to zero in $H^2(W,F_2|_W)$, hence equals $a_*(d_1)$ for some
$d_1\in H^2(W,F_1|_W)$. Choose $y_1\in H^2(X,F_1)$ restricting to $d_1$.
Then $x+a_*(y_1)$ restricts to $c$. This proves the eighth assertion and
completes all eight cases compressed in Tag `0A5C`.

## Detailed form

Let

$$
 0\longrightarrow F_1\longrightarrow F\longrightarrow F_2
 \longrightarrow0
$$

be exact in $\Ab(C_{\Et})$. If $\mathcal C(C,F_1)$ and $\mathcal C(C,F_2)$
hold in the sense of [def-weil-pbc-eight-curve-assertions], then
$\mathcal C(C,F)$ holds. In particular, the class of torsion sheaves
satisfying all eight implications is closed under extensions.

## Proof

For $1\leq j\leq7$, the assertion $\mathcal C_j$ is preserved by short exact
sequences: the long exact cohomology sequences of $0\to F_1\to F\to F_2\to0$
and the five lemma pass the vanishing statements (C1)--(C3) to $F$, give
finiteness of the middle group in (C4) and (C5) (cokernels and kernels of maps
of finite groups are finite), and give the isomorphism statements (C6) and
(C7) once the pullback maps $\rho^q_{k'/k}$ form a natural map of the two long
exact sequences.

For (C8), fix any open immersion $a:U\hookrightarrow C$ and a class $b\in
H^2(U,a^{-1}F)$. Denote its image in $H^2(U,a^{-1}F_2)$ by $b_2$. Assertion
(C8) for $F_2$ gives $c_2\in H^2(C,F_2)$ with $a^*c_2=b_2$. The obstruction to
lifting $c_2$ to $H^2(C,F)$ lies in $H^3(C,F_1)$, which is zero by (C1) for
$F_1$. Choose a lift $c\in H^2(C,F)$. Naturality of the long exact sequences
under restriction shows that $b-a^*c$ maps to zero in $H^2(U,a^{-1}F_2)$.
Exactness therefore gives $b_1\in H^2(U,a^{-1}F_1)$ whose image is $b-a^*c$.
Apply (C8) for $F_1$ to choose $c_1\in H^2(C,F_1)$ restricting to $b_1$. If
$\iota_*:H^2(C,F_1)\to H^2(C,F)$ is induced by $F_1\hookrightarrow F$, then

$$
 a^*(c+\iota_*c_1)=a^*c+(b-a^*c)=b.
$$

This proves (C8) for $F$, without a hypothesis on the components of $U$. Thus
$\mathcal C(C,F)$ holds.
