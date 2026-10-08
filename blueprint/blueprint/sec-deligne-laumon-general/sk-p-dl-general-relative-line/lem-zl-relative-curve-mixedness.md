+++
id = "lem-zl-relative-curve-mixedness"
kind = "lemma"
title = "Mixedness of the direct images over a relative affine curve"
order = 2843
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-qbar-category", "def-weil-pbc-scheme-conventions", "def-weil-punctual-weights", "def-weil-scheme-morphism-properties", "def-wf-constant-weil-twist", "def-wf-normalized-real-envelope", "lem-a1-mixed-direct-summand", "lem-wf-constant-twist-cohomology", "lem-wf-envelope-real", "lem-zl-relative-envelope-factor-reality", "sbc-thm-finiteness-finite-type", "thm-cbc-qbar", "thm-zl-real-mixed-by-curves"]
+++
Fix the coefficient and weight conventions of
[def-weil-punctual-weights]. Let $h:U_0\to Y_0$ be a
smooth separated morphism
between separated finite-type
$k_0$-schemes, with every nonempty geometric fiber a smooth affine curve,
and let $\mathcal F$ be a
lisse
$\Qlb$-Weil sheaf that is
punctually $\iota$-pure of weight
$w$. Then for every $i$ there is a real number $u_i$ such that
$R^ih_!\mathcal F$ is
$\iota$-mixed of weights at most
$u_i$.
The proof follows the reduction in Kiehl–Weissauer I.7, pp. 53–54:
the curve bound separates the two cohomological root radii, and
[thm-zl-real-mixed-by-curves] supplies mixedness on the base by
geometric reduction to the already proved real-sheaf theorem on curves.
No instance of the general direct-image weight theorem is imported.

## Proof

Normalize $\mathcal F$ as in
[def-wf-normalized-real-envelope]: put
$b=\iota^{-1}(q^{-w/2})$,
$\mathcal F^0=\mathcal F\otimes\mathcal B_b$, and
$\mathcal E=\mathcal F^0\oplus(\mathcal F^0)^\vee$.
It is lisse, pure of weight zero and real by
[lem-wf-envelope-real]. The relative factor calculation
[lem-zl-relative-envelope-factor-reality], which uses only the
proved curve estimate, shows that $R^ih_!\mathcal E$ is real for
every $i$. These are constructible sheaves: the finite-level
finiteness theorem [sbc-thm-finiteness-finite-type] supplies the
constructible landing hypotheses in the coefficient passage of
[thm-cbc-qbar].

Apply [thm-zl-real-mixed-by-curves] on $Y_0$, obtaining a
finite mixed filtration of $R^ih_!\mathcal E$.
Additivity makes $R^ih_!\mathcal F^0$ a direct summand, so it is
mixed by [lem-a1-mixed-direct-summand]. The constant-twist
projection formula [lem-wf-constant-twist-cohomology] identifies

$$
R^ih_!\mathcal F
\cong R^ih_!\mathcal F^0\otimes\mathcal B_{b^{-1}}.
$$

Tensoring the finite filtration with this rank-one sheaf is exact.
At a closed point of degree $m$, the twist multiplies each
eigenvalue by $b^{-m}$, of $\iota$-modulus $q^{mw/2}$, by
[def-wf-constant-weil-twist]. Thus every pure quotient of weight
$v$ becomes pure of weight $v+w$, including where its stalk is
zero. This gives the required finite mixed filtration without a
lissity assumption on the direct image. Its finitely many
weights have a maximum $u_i$; for the zero sheaf take any $u_i$.
