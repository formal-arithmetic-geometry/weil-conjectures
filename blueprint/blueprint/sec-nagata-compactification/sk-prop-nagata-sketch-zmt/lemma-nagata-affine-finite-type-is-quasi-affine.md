+++
id = "lemma-nagata-affine-finite-type-is-quasi-affine"
kind = "lemma"
title = "Affine schemes are quasi-affine"
order = 186
lean = ["AlgebraicGeometry.Scheme.instIsQuasiAffineOfIsAffine"]
uses = ["lemma-nagata-quasi-affine-immersion-affine-space-exists"]
+++
If $U$ is affine, then $U$ is quasi-affine in the sense used in
[lemma-nagata-quasi-affine-immersion-affine-space-exists]; in
particular that lemma applies to any $U\to S$ of finite type with $U$
affine.

## Proof

The identity of $U$ realizes the canonical map
$U\to\operatorname{Spec}\Gamma(U,\mathcal O_U)$ as an open immersion, and
$U$ is quasi-compact. This is the defining quasi-affine property, and a
finite-type structure morphism is in particular locally of finite type.
