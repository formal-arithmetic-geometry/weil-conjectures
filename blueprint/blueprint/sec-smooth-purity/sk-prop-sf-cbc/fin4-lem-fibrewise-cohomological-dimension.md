+++
id = "fin4-lem-fibrewise-cohomological-dimension"
kind = "lemma"
title = "Cohomological dimension over an algebraically closed field"
order = 1591
uses = ["def-weil-pbc-constructible-complexes", "def-weil-pbc-etale-cohomology", "def-weil-pbc-scheme-conventions", "lem-exc-field-discrete-modules", "sbc-def-coefficient-conventions", "thm-sc-finite-type-torsion-cd"]
+++
Let $k'$ be algebraically closed, let $X$ be a
finite-type $k'$-scheme
of dimension at most $d$, and let $F$ be a
constructible
$\Lambda$-sheaf, with finite coefficients as in
[sbc-def-coefficient-conventions].
Then $H^q(X_{\rm et},F)=0$ for $q>2d$, with cohomology
as in [def-weil-pbc-etale-cohomology].

## Proof

The coefficient ring of [sbc-def-coefficient-conventions]
is killed by a positive integer, so $F$ is torsion.
The absolute Galois group of $k'$ is trivial; the field
dictionary of [lem-exc-field-discrete-modules] therefore
gives torsion cohomological dimension zero for $k'$.
Apply [thm-sc-finite-type-torsion-cd] with $c=0$.
It proves the stronger assertion for all torsion etale sheaves.
Its proof uses Zariski Leray and the affine ordinary
cohomological-dimension theorem; no compact-support
identification or affine compact-support bound is involved.
