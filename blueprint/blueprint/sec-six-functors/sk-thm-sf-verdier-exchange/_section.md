+++
id = "sk-thm-sf-verdier-exchange"
kind = "section"
title = "Verdier-duality exchange"
order = 2170
uses = ["sk-def-sf-operations", "sk-lem-sf-mate", "sk-thm-sf-comp-composition", "sk-thm-sf-tensor-hom"]
lean = ["AlgebraicGeometry.Etale.nonempty_iso_verdierDual_rightDerivedLowerShriek", "AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_dualizingComplex"]
+++
*Theorem (sketch).*

Let $f:X\to Y$ be a separated finite-type morphism of finite-type $k$-schemes,
with $Rf^!$ and the dualizing complexes $\omega_X=Ra_X^!\Lambda$,
$\omega_Y=Ra_Y^!\Lambda$ formed with the constructible exceptional adjoint of
[sk-def-sf-operations](vi) (no admissibility datum is assumed).
Then $Rf^!\omega_Y\cong\omega_X$, and for $M\in\Dctf(X,\Lambda)$ there is a canonical isomorphism

$$
\mathbb D_Y(Rf_!M)\xrightarrow{\ \sim\ }Rf_*\mathbb D_X(M),
$$

in the ambient category $D^+(Y,\Lambda)$, natural in $M$ and compatible with
finite reduction, scalar extension and shifts.

## Proof

*Step 1:* $Rf^!\omega_Y\cong\omega_X$: by the composition law and
[sk-lem-sf-mate], the mate of $R(a_Y\circ f)_!\cong Ra_{Y!}Rf_!$ is the
isomorphism $Rf^!Ra_Y^!\cong Ra_X^!$. *Step 2:* apply
[sk-thm-sf-tensor-hom] with $N=\omega_Y$ and substitute Step 1:
$\mathbb D_Y(Rf_!M)=\RHom_Y(Rf_!M,\omega_Y)\cong Rf_*\RHom_X(M,f^!\omega_Y)\cong Rf_*\RHom_X(M,\omega_X)=Rf_*\mathbb D_XM$.
Naturality and the compatibilities are those of the two ingredients. (This
proof uses only the tensor–Hom exchange and never the duality chapter, which
is what removes the proof cycle between the framework and duality chapters.)

Uses: `\Cref{sk-def-sf-operations}`, `\Cref{lem-sf-mate}`, `\Cref{sk-thm-sf-tensor-hom}`, `def-weil-exceptional-inverse-image`
