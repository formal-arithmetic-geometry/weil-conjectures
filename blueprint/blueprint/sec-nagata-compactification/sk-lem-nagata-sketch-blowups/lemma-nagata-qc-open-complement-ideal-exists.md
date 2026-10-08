+++
id = "lemma-nagata-qc-open-complement-ideal-exists"
kind = "lemma"
title = "Existence of an ideal defining the complement of a qc open"
order = 168
lean = ["AlgebraicGeometry.Scheme.exists_finiteType_ideal_coe_support_eq_compl"]
uses = ["def-nagata-extended-ideal", "lemma-nagata-finite-type-ideal-extension-exists"]
+++
Let $W\subseteq Y$ be a quasi-compact open in a qcqs scheme. There exists
a finite type quasi-coherent ideal $\mathcal I\subseteq\mathcal O_Y$ such
that $V(\mathcal I)=Y\setminus W$.

## Proof

Let $\mathcal K\subseteq\mathcal O_Y$ be the quasi-coherent ideal defining
the reduced induced closed subscheme on $Y\setminus W$. Its restriction to
$W$ is the unit ideal. Apply the general submodule form of
[lemma-nagata-finite-type-ideal-extension-exists] with ambient module
$\mathcal K$ and submodule $\mathcal O_W=\mathcal K|_W$. It gives a finite
type quasi-coherent submodule $\mathcal I\subseteq\mathcal K$ with
$\mathcal I|_W=\mathcal O_W$. As an $\mathcal O_Y$-submodule of the ideal
$\mathcal K$, the sheaf $\mathcal I$ is itself an ideal.
The inclusion $\mathcal I\subseteq\mathcal K$ gives
$Y\setminus W=V(\mathcal K)\subseteq V(\mathcal I)$, while
$\mathcal I|_W=\mathcal O_W$ gives the reverse containment. Hence
$V(\mathcal I)=Y\setminus W$.
