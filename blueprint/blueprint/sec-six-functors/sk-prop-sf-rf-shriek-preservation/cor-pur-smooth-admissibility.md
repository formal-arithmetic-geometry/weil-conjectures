+++
id = "cor-pur-smooth-admissibility"
kind = "theorem"
title = "Smooth morphisms satisfy the preservation clauses"
order = 2077
tags = ["latex:corollary"]
uses = ["cor-pur-dualizing-object-purity", "cor-sf-ambient-adjoint-discharge", "def-coefficient-twists-detailed", "def-pur-conventions", "def-sbc-smooth-morphisms", "def-weil-ambient-exceptional-adjoint", "def-weil-constructible-intervals", "def-weil-exceptional-adjoint-admissibility", "def-weil-finite-tor-amplitude", "def-weil-finite-torsion-constructibility", "def-weil-scheme-morphism-properties", "lem-exc-residue-tor-test", "lem-weil-field-tor-amplitude", "prop-weil-pbc-inverse-image-exact", "prop-weil-twist-preserves", "thm-asd-smooth-tensor", "thm-cbc-finite-level-proetale", "thm-pur-diagonal-dualizing-object", "thm-sf-ambient-adjoint-class"]
+++
In the purity conventions of this chapter ([def-pur-conventions] fixed setting),
let $f:X\to Y$ be smooth separated of pure relative dimension $d$.
The
ambient exceptional right
adjoint datum of [def-weil-ambient-exceptional-adjoint] was the
hypothesis under which this corollary was formerly stated; it is not assumed
here, being on the bounded constructible and finite-Tor coefficients that the
two clauses below quantify over the theorem
[cor-sf-ambient-adjoint-discharge]. Then $f$ satisfies the
two preservation clauses of
[def-weil-exceptional-adjoint-admissibility], with
$c_f^-=c_f^+=-2d$ in the signed convention of that definition:

1. *constructibility.* For all integers $a\leq b$,
$$
L\in D_c^{[a,b]}(Y,A)\quad\Longrightarrow\quad
Rf^!L\in D_c^{[a-2d,b-2d]}(X,A).
$$
1. *finite Tor amplitude.* If $K\in D^b_{ctf}(Y,A)$ has
finite Tor amplitude in
$[a,b]$, then $Rf^!K$ has finite Tor amplitude in
$[a-2d,b-2d]$; in particular $Rf^!$ carries $D^b_{ctf}(Y,A)$
into $D^b_{ctf}(X,A)$.

Thus every smooth morphism is
exceptional-adjoint admissible at $A=A_{E,n}$ in the constructible sense —
the three clauses of [def-weil-exceptional-adjoint-admissibility] read on the
complexes of the blueprint's coefficient class that the two clauses below
quantify over; the unrestricted clause (1) of that definition, on all
pro-etale sheaves, is false in general and is not asserted —: the
preservation
clauses are consequences of purity, not hypotheses of it, and the ambient
datum that the earlier form of this corollary assumed is not an assumption
either, by [cor-sf-ambient-adjoint-discharge]. The weaker statement
``admissible at $\Lambda\in\{\mathcal O_E,E,\Qlb\}$'' demands in addition the
uniformity of the two clauses over the finite stages and the
finite-reduction and scalar-extension compatibilities of the right adjoints;
those are the coefficient transport of the transport section at the end of
this chapter, and they are *not* asserted here.

## Proof

By [cor-pur-dualizing-object-purity] the right adjoint $Rf^!$, whose
existence on the coefficients used here is the theorem
[cor-sf-ambient-adjoint-discharge], is
identified with $Lf^*(-)(d)[2d]$ on finite-Tor objects. For a
bounded constructible complex $L$ without finite Tor amplitude, use
the tensor formula on all ordinary etale complexes of
[thm-asd-smooth-tensor], the orientation at $\Lambda$ of
[thm-pur-diagonal-dualizing-object], and the comparison
[thm-sf-ambient-adjoint-class]. They give the same identification
for $L$; no site-perfectness of $L$ is assumed. The criterion below is
applied at the finite etale level and transported to the small pro-etale
site along [thm-cbc-finite-level-proetale], as elsewhere in this
chapter.
Step 1: (1). The inverse image of [prop-weil-pbc-inverse-image-exact] is exact.
It preserves constructibility: pull back each finite stratification
and each finite locally constant sheaf on its strata, as in
[def-weil-finite-torsion-constructibility]. Thus for
$L\in D_c^{[a,b]}(Y,A)$ the complex $Lf^*L$ is bounded constructible
with $\mathcal H^r(Lf^*L)\cong f^*\mathcal H^r(L)$, which vanishes for
$r\notin[a,b]$; the [def-coefficient-twists-detailed] twist preserves the
vanishing degrees by [prop-weil-twist-preserves], and the shift moves them, by the convention
$\mathcal H^r(C[2d])=\mathcal H^{r+2d}(C)$, to $[a-2d,b-2d]$.
Step 2: (2). Test the finite Tor amplitude of $Rf^!K$ by the residue
field criterion of [lem-exc-residue-tor-test]: it is equivalent to
the complex $\mathcal H^\bullet\bigl(Rf^!K\otimes^L_A\kappa\bigr)$ being
concentrated in $[a-2d,b-2d]$. Substituting the purity
identification and the associativity of the derived tensor product,

$$
Rf^!K\otimes^L_A\kappa
\;\cong\;\bigl(Lf^*K\otimes^L_A\kappa\bigr)(d)[2d]
\;\cong\;Lf^*\bigl(K\otimes^L_A\kappa\bigr)(d)[2d].
$$

By the same criterion applied to $K$, the complex
$K\otimes^L_A\kappa$ has cohomology in $[a,b]$; the inverse image
$Lf^*$ is exact, so $Lf^*(K\otimes^L_A\kappa)$ has cohomology in
$[a,b]$, and the twist by the locally constant free rank-one sheaf
$\Lambda(d)$ preserves the vanishing degrees. The shift therefore puts
the cohomology in $[a-2d,b-2d]$, which is the assertion. At field
coefficients the assertion is the case already recorded in
[lem-weil-field-tor-amplitude].
