+++
id = "prop-weil-pbc-gabber-affine-comparison"
kind = "theorem"
title = "Gabber affine comparison"
order = 1134
tags = ["latex:proposition"]
uses = ["def-weil-pbc-etale-sheaves", "def-weil-pbc-henselian-terminology", "def-weil-pbc-scheme-conventions", "lemma-weil-pbc-etale-degree-zero", "lemma-weil-pbc-gabber-effacement"]
+++
For an affine henselian pair $(T,T_0)$ and torsion $F$,
$H^q(T,F)\xrightarrow{\sim}H^q(T_0,F_0)$ for all $q\geq0$.

## Proof

Degree zero is the etale henselian restriction lemma applied on the affine.
For $q>0$, assume comparison in all degrees below $q$. To prove injectivity,
take a nonzero $\xi\in H^q(T,F)$ and apply effacement with closed subscheme
$T$ itself, obtaining $F\hookrightarrow F'$ in which $\xi$ dies. Put
$Q=F'/F$. Exactness lifts $\xi$ from $H^{q-1}(T,Q)$. The induction
isomorphism in degree $q-1$ carries any such lift to $T_0$; if $\xi$ restricted
to zero, exactness and the commutative boundary square would force the lift
to come from $H^{q-1}(T,F')$, contradicting the choice of nonzero $\xi$.

For surjectivity, take $\eta\in H^q(T_0,F_0)$ and use effacement with closed
subscheme $T_0$ to choose $F\hookrightarrow F'$ killing $\eta$. Exactness
lifts $\eta$ from $H^{q-1}(T_0,Q_0)$. By induction this lift is the
restriction of a class in $H^{q-1}(T,Q)$, whose boundary in $H^q(T,F)$
restricts to $\eta$. Thus the comparison is separately injective and
surjective. This expands Tag `09ZI`; no statement is imported from
that tag.

## Detailed form

Let $(A,I)$ be an affine henselian pair and let $X$ be an affine scheme of
finite type over $\operatorname{Spec}A$, with closed fibre
$X_0=X\times_{\operatorname{Spec}A}\operatorname{Spec}(A/I)$. Then for every
torsion etale sheaf $F$ on $X$,

$$
 H^q(X,F)\xrightarrow{\sim}H^q(X_0,F_0)
 \qquad(q\geq0).
$$

The case $X=\operatorname{Spec}A$ is the comparison for the affine henselian
pair $(T,T_0)=(\operatorname{Spec}A,\operatorname{Spec}(A/I))$ itself. The
relative form is the one used below: the affine charts of a finite-type
$A$-scheme are affine of finite type over $A$, but they are *not* themselves
henselian pairs, so the pair form alone does not apply to them.

**Status.** This is the cited Gabber input (Stacks Project, Theorem 59.82.7,
Tag [09ZI](https://stacks.math.columbia.edu/tag/09ZI)); its formal
consequences are proved below in this section. The former effacement
statements of this chapter were retired, since no proof uses them.

## Proof

The statement is the input recorded in the reference: the Gabber comparison
for affine henselian pairs, i.e. that for an affine henselian pair $(T,T_0)$
and a torsion etale sheaf $F$ on $T$, the restriction map $H^q(T,F)\to
H^q(T_0,F_0)$ is an isomorphism for every $q\geq0$ (Stacks Project, Theorem
59.82.7, Tag [09ZI](https://stacks.math.columbia.edu/tag/09ZI)). Its proof is
the effacement argument: by induction on $q$, classes of degree $q>0$ are
killed by the effacement step, giving injectivity, and the induction step
builds the extension of classes of degree $q-1$ from $T_0$ to $T$, giving
surjectivity. The blueprint isolates this single assertion, proves separately
its formal consequences (degree-zero comparisons over henselian pairs, and the
acyclicity bound for restricted injectives), and does not discharge it here.
