+++
id = "lem-fd-as-lisse"
kind = "lemma"
title = "Multiplicativity of the Artin–Schreier sheaves"
order = 2685
lean = ["AlgebraicGeometry.Etale.isLocallyConstantSheaf_artinSchreierSheaf", "AlgebraicGeometry.Etale.artinSchreierSheafAddIso", "AlgebraicGeometry.Etale.artinSchreierSheafZeroIso"]
uses = ["lem-fd-as-characters"]
+++
The sheaf $\mathcal L_{\psi,f}$ is lisse of rank one on $X_0$, and

$$
\mathcal L_{\psi,f}\otimes\mathcal L_{\psi,g}\cong\mathcal L_{\psi,f+g},\qquad
(\mathcal L_{\psi,f})^{-1}\cong\mathcal L_{\psi,-f}\cong\mathcal L_{\psi^{-1},f}.
$$

This is the second assertion of [lem-fd-as-characters].

## Proof

This is immediate from the decomposition of [lem-fd-as-characters] (the tensor and inverse of the rank-one isotypic components correspond to the sums $f+g$ and $-f$ of the functions).
