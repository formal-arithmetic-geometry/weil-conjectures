+++
id = "prop-weil-pbc-koszul-reconstruction"
kind = "theorem"
title = "Koszul and quotient reconstruction"
order = 1248
uses = ["def-weil-pbc-adic-coefficient-datum"]
tags = ["latex:proposition"]
+++
For the strict quotient tower $K_\bullet$ of
[def-weil-pbc-adic-coefficient-datum] there is a functorial isomorphism

$$
 K^{\wedge}_{\mathrm{Kos}}\xrightarrow{\sim}\Rlim K_\bullet
$$

carrying the Koszul completion map to the quotient-tower completion map
$K\to\Rlim K_\bullet$. Every derived $I$-complete object consequently
satisfies

$$
 K\xrightarrow{\sim}\Rlim K_\bullet.
$$

(*Source: the adic reconstruction, i.e. the identification of the
Koszul-derived completion with the derived limit over the Koszul tower
$K_\bullet(A,f_1^n,\dots,f_r^n)$ of the generators (not over the quotient
tower $A/I^n$, which is not quasi-isomorphic to it in general), is the
derived-completion formalism of Stacks Project, More on Algebra, Section
15.93 (Derived Completion), Tag
[091N](https://stacks.math.columbia.edu/tag/091N), with Lemma 15.93.17, Tag
[091Z](https://stacks.math.columbia.edu/tag/091Z). The same identification
over the quotient tower, in the constant Noetherian case, is Stacks Project,
Lemma 61.20.1 (Tag [099M](https://stacks.math.columbia.edu/tag/099M), Section
61.20, Tag [099L](https://stacks.math.columbia.edu/tag/099L)), whose proof
passes through the Koszul pro-system $K(\Lambda,f_1^n,\dots,f_r^n)$ and
concludes $K^\wedge=\Rlim(K\otimes^L_\Lambda\underline{\Lambda/I^n})$: the
Stacks entry assumes a Noetherian ring $\Lambda$ and an ideal
$I\subset\Lambda$ on an arbitrary site, while the form used here is the
reconstruction over a finite extension $E/\Ql$ with $A=\mathcal O_E$,
$I=(\varpi)$.*)

## Proof

This is the recorded classical input of the statement, the derived-completion
formalism of Stacks Project, More on Algebra, Section 15.93 (Tag
[091N](https://stacks.math.columbia.edu/tag/091N)): the Koszul-derived
completion of a complex and the derived limit over its strict quotient tower
compute the same object, and both completion maps are the canonical ones. The
blueprint uses the identification as the defining property of the adic
coefficient datum of [def-weil-pbc-adic-coefficient-datum] and gives no
separate proof.
