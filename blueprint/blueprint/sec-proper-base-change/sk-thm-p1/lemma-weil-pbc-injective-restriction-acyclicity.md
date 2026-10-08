+++
id = "lemma-weil-pbc-injective-restriction-acyclicity"
kind = "lemma"
title = "Injective restriction acyclicity bound"
order = 1135
uses = ["def-weil-pbc-henselian-terminology", "def-weil-pbc-scheme-conventions", "prop-weil-pbc-gabber-affine-comparison"]
+++
Let a separated scheme with affine diagonal be covered by $n+1$ affine opens.
If $I$ is injective on the scheme over a henselian pair, then the restriction
to the closed fibre has vanishing cohomology in degrees $>n$.

## Proof

For $n=0$ this is the affine comparison applied to the injective $I$. For
$n>0$, split the cover as $U_0$ and $V=\bigcup_{i>0}U_i$. The Mayer–Vietoris
long exact sequence for $U_0\cup V$ has terms on $U_0$, $V$, and
$U_0\cap V$; the last two have covers of size at most $n$ and the affine
comparison kills their groups above the inductive bound. The long exact
sequence therefore kills the group above degree $n$. This is the dimension
induction located at Tag `0A51`.

## Detailed form

Let $(A,I)$ be an affine henselian pair, let $Y$ be separated of finite type
over $\operatorname{Spec}A$ with affine diagonal, covered by $n+1$ affine
opens, and let $Y_0=Y\times_{\operatorname{Spec}A}\operatorname{Spec}(A/I)$.
If $I$ is injective on $Y_{\Et}$, then

$$
 H^q(Y_0,I|_{Y_0})=0\qquad(q>n).
$$

## Proof

Each affine open $U\subseteq Y$ is affine of finite type over
$\operatorname{Spec}A$, and its closed fibre is $U_0=U\times_YY_0$, so
Gabber's affine comparison in the relative form
[prop-weil-pbc-gabber-affine-comparison] gives $H^q(U_0,I|_U)\cong
H^q(U,I|_U)$; an injective sheaf on an affine scheme has no higher cohomology,
so $H^q(U_0,I|_U)=0$ for $q>0$. This is the case $n=0$; the hypothesis that
the charts are affine over the henselian pair, and not the false assertion
that they are themselves henselian pairs, is what makes the comparison
applicable. For the induction step write $Y=U\cup V$ with $U$ affine and $V$
covered by $n$ affine opens; the intersection $U\cap V$ is affine because $Y$
is separated with affine diagonal, and the Mayer--Vietoris long exact sequence
of the closed fibre

$$
 \cdots\to H^q((U\cup V)_0,-)\to H^q(U_0,-)\oplus H^q(V_0,-)
 \to H^q((U\cap V)_0,-)\to\cdots
$$

together with the induction hypothesis for $V$ and for $U\cap V$ gives the
vanishing for $q>n$. The restriction of an injective sheaf to an open
subscheme is injective on the small etale site, so the induction hypothesis
applies to $V$, to $U\cap V$ and to each chart separately.
