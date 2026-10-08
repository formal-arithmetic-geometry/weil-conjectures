+++
id = "lemma-nagata-partial-union-overlap-dense"
kind = "lemma"
title = "Density needed for induction on the affine cover"
order = 323
lean = ["Dense.preimage_val_inter"]
uses = ["def-nagata-partial-affine-unions", "lemma-nagata-dense-affine-cover"]
+++
For $r>1$, the overlap $X_{r-1}\cap U_r$ is dense in $X_r$.

## Proof

The overlap contains $D_X$. Since $X_r$ is open in $X$ and $D_X$ is dense
in $X$, it is dense in $X_r$; therefore the larger subset
$X_{r-1}\cap U_r$ is dense in $X_r$.
