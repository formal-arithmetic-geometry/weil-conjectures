+++
id = "sk-def-ia"
kind = "section"
title = "Injective acyclicity"
order = 1049
lean = ["AlgebraicGeometry.Etale.HasInjectiveAcyclicity"]
uses = ["sk-def-conv", "sk-def-exchange"]
+++
*Definition (sketch).*

For a proper morphism $f:X\to Y$ and a prime
$r$, write $\mathrm{IA}_r(f)$ if for every base change
$g:Y'\to Y$ — with $f':X'\to Y'$ and $g':X'\to X$ the two other
sides of the cartesian square of [sk-def-exchange], so that
$X'=X\times_YY'$, $f'$ is the base change of $f$ and $g'$ the base
change of $g$ — every injective sheaf $I$ of $\Fq$-modules on
$X_{\Et}$ satisfies

$$
R^qf'_*\,g'^{-1}I=0\qquad(q>0),
$$

and $\mathrm{IA}(f)$ for all primes.

Uses: [sk-def-conv], [sk-def-exchange]
