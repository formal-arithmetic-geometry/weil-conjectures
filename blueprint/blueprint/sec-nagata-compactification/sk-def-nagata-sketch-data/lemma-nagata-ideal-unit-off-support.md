+++
id = "lemma-nagata-ideal-unit-off-support"
kind = "lemma"
title = "The center ideal is the unit ideal off its support"
order = 57
lean = ["AlgebraicGeometry.Scheme.IdealSheafData.ideal_eq_top_of_disjoint_support"]
+++
If $Z=V(\mathcal I)$ and $U=X\setminus Z$, then
$\mathcal I|_U=\mathcal O_U$.

## Proof

At a point outside $V(\mathcal I)$, the stalk $\mathcal I_x$ is not
contained in the maximal ideal of $\mathcal O_{X,x}$, so it contains a unit
and equals $\mathcal O_{X,x}$. Equality of quasi-coherent ideals can be
checked on stalks.
