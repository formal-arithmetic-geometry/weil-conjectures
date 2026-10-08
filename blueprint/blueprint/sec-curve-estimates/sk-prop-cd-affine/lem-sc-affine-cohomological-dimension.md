+++
id = "lem-sc-affine-cohomological-dimension"
kind = "lemma"
title = "Cohomological dimension of a smooth affine curve"
order = 1018
uses = ["def-sc-curves", "def-weil-pbc-etale-cohomology", "def-weil-pbc-etale-sheaves", "lem-sc-affine-generic-second", "lem-sc-cohomological-dimension", "lem-sc-generic-cohomology-comparison"]
+++
For a smooth affine connected curve $C$
over an algebraically closed field and any torsion
etale sheaf $F$,
one has $H^q(C,F)=0$ for $q>1$, with cohomology as in
[def-weil-pbc-etale-cohomology].

## Proof

The degrees $q>2$ vanish by [lem-sc-cohomological-dimension].
In degree two, work componentwise and apply
[lem-sc-generic-cohomology-comparison] with $M=\eta^*F$;
the resulting group $H^2(C,\eta_*M)$ vanishes by
[lem-sc-affine-generic-second].
