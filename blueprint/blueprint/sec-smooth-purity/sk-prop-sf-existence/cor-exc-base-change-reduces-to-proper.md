+++
id = "cor-exc-base-change-reduces-to-proper"
kind = "theorem"
title = "Base change for a general morphism reduces to the proper part"
order = 1812
tags = ["latex:corollary"]
uses = ["cor-sf-ambient-adjoint-discharge", "def-sf-fullcd-used-class", "def-weil-ambient-exceptional-adjoint", "def-weil-compactifications-refinements", "def-weil-pbc-derived-categories", "def-weil-pbc-inverse-image"]
+++
Let $f:X\to Y$ be separated finite type with a
compactification
$X\xrightarrow{j_0}\overline X\xrightarrow{p}Y$, and let $g:Y'\to Y$
be arbitrary. If the base-change comparison
$L\overline g^*Rp^{\times}\to R(p')^{\times}Lg^*$ is an isomorphism for
the proper morphism $p$, then the base-change comparison
$Lg'^*Rf^{\times}\to Rf'^{\times}Lg^*$ is an isomorphism for $f$.
Consequently the comparison for a general separated finite-type morphism
is reduced to its proper part, the open part being free. The ambient
exceptional right adjoint datum that the identity $Rf^{\times}\cong j_0^*Rp^{\times}$ uses is, on the blueprint's coefficient class
[def-sf-fullcd-used-class], the theorem
[cor-sf-ambient-adjoint-discharge], so the reduction is unconditional
there.

## Proof

The compact-support functor is $Rf_!=Rp_!j_{0!}=Rp_*j_{0!}$, so by
uniqueness of right adjoints — the uniqueness invoked in the ambient
datum of [def-weil-ambient-exceptional-adjoint] — the ambient right
adjoint is
$Rf^{\times}\cong j_0^*Rp^{\times}$, and likewise
$Rf'^{\times}\cong j_0'^*R(p')^{\times}$ for the base change. The
base-change comparison for $f$ is therefore, by pullback composition
([def-weil-pbc-inverse-image]), the comparison for $p$ conjugated
by the isomorphisms $Lg'^*j_0^*\cong j_0'^*L\overline g^*$; it is an
isomorphism whenever the comparison for $p$ is.
