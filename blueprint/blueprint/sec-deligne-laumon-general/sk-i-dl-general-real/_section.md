+++
id = "sk-i-dl-general-real"
kind = "section"
title = "Real sheaves on an arbitrary base"
order = 2829
lean = ["AlgebraicGeometry.WeilSheaf.IsReal.isMixed"]
uses = ["sk-d-dl-general-weights", "sk-d-real-weights", "sk-i-topology", "sk-l-dl-general-quasifinite", "sk-p-real-integral", "sk-p-real-purity", "sk-p-real-rankone", "sk-prop-sf-open-closed-triangle"]
+++
*Proposition (sketch).*

Every constructible $\iota$-real Weil sheaf on a separated finite-type
$k_0$-scheme is $\iota$-mixed. Here real means that all realized local
Frobenius characteristic polynomials have real coefficients.

## Proof

*Reduction to a lisse stratum.*
By Noetherian induction and invariance under nilpotents, it suffices
to make a lisse real sheaf $G_0$ on a smooth affine irreducible stratum
mixed on a dense open. Dimension zero follows from Frobenius eigenspaces.
A finite constant extension splits geometric components and makes the
Weil constituents geometrically irreducible: the geometric socle spans
each irreducible Weil representation, Frobenius permutes its isotypic
blocks, and an eigenline for the multiplicity action of a Frobenius
power gives the required factors. Descent is justified below.

*A determinant weight independent of the curve.*
For a rank-one lisse sheaf $L_0$ on the resulting geometrically connected
$X_0$, join any two closed points by a geometrically irreducible curve:
use $X_0$ in dimension one and
[Charles–Poonen,
Corollary 1.9](https://math.mit.edu/~poonen/papers/bertini_irred.pdf) in higher dimension. Its reduced normalization is smooth
and geometrically connected. By [sk-p-real-rankone], the pullback of
$L_0$ is pure. Residue extensions raise Frobenius and residue cardinality
to the same powers, so the normalized weights at the two points agree.
Thus every $L_0$ has one weight, and for each constituent $V_0$,

$$
d(V_0)=\frac{\operatorname{wt}_\iota(\det V_0)}
{\operatorname{rank}V_0}
$$

is independent of the slicing curve.

*Purity on a dense open from Section [sec-purity-real-sheaves].*
The irreducibility-preserving Bertini theorem
([Kiehl–Weissauer](https://doi.org/10.1007/978-3-662-04576-3),
Appendix B, Theorem 1, in the form recalled in Complete notes, §9.4)
provides, after a sufficiently ample embedding, an open family of smooth
geometrically irreducible curve sections on which $V$ stays irreducible;
these cover a dense open of $X$. Each is defined over a finite constant
extension. The restriction of $G_0$ remains real because conjugate
eigenvalues have conjugate powers. Its irreducible constituent $V_0$
therefore becomes pure by [sk-p-real-purity], with the same weight
$d(V_0)$ on every curve. Hence $V_0$ is pure on the covered open.
Intersect the finitely many opens and their Galois conjugates; a
composition filtration makes $G_0$ mixed there.

*Descent and the closed complement.*
For a finite constant extension $g:X'_0\to X_0$, the adjunction map
$G_0\to g_*g^*G_0$ is split by the trace divided by $\deg g$.
The quasi-finite lemma shows that $g_*$ preserves mixedness, so
mixedness descends to the original dense open. If $j_0$ is this open
and $i_0$ its closed complement, use

$$
0\longrightarrow j_{0!}j_0^*G_0\longrightarrow G_0
\longrightarrow i_{0*}i_0^*G_0\longrightarrow0.
$$

The open term is mixed by extension by zero; the closed term is mixed
by induction. Splicing their filtrations proves the proposition.

Uses: [sk-d-dl-general-weights], [sk-d-real-weights], [sk-l-dl-general-quasifinite], [sk-p-real-purity], [sk-p-real-rankone], [sk-prop-sf-open-closed-triangle]
