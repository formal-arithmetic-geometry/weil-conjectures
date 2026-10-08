+++
id = "lem-fin-generic-radicial-smoothing"
kind = "lemma"
title = "A smooth dense open after a finite radicial base change"
order = 1635
uses = ["def-sbc-smooth-morphisms", "def-weil-pbc-constructible-complexes", "def-weil-pbc-scheme-conventions"]
+++
Let $S$ be integral of finite type over a field and let
$X\to S$ be of finite type with $X\ne\varnothing$.
After shrinking $S$, there is a finite radicial surjection
$S'\to S$ such that $(X_{S'})_{\mathrm{red}}$ has a dense
open $V$ smooth over $S'$. For a constructible finite sheaf
$F$ on $X$, one may require its pullback to $V$ to be
locally constant. Every component of the complement in the
generic fiber then has dimension strictly smaller than the
dimension of the component of $X_{S'}$ that contains it.
The notation refers to scheme conventions.

## Proof

Write $K=k(S)$. In characteristic zero put $K'=K$.
In characteristic $p>0$, pass first to the perfect closure
$K^{\mathrm{perf}}$. The reduced finite-type
$K^{\mathrm{perf}}$-scheme $(X_{K^{\mathrm{perf}}})_{\mathrm{red}}$
has a dense smooth open. Indeed, at every generic point choose
a separating transcendence basis of its finitely generated
residue field over the perfect field; a primitive element for
the remaining finite separable extension has nonzero derivative.
Inverting that derivative and the finitely many denominators in
a finite presentation gives a smooth neighborhood by the
Jacobian criterion in [def-sbc-smooth-morphisms].
The neighborhoods cover all generic points.

This construction uses finitely many coefficients: generators
of the nilpotent ideal defining the reduction, equations for
the finitely many chosen open neighborhoods, and the indicated
Jacobian identities. They lie in a finite purely inseparable
extension $K'/K$. Enlarging $K'$ once more if necessary,
the descended ideal is nilpotent (use one common power for its
finitely many generators), and the descended opens are smooth
by the same Jacobian identities. Their union contains every
generic point, since this can be checked after the faithfully
flat field extension to $K^{\mathrm{perf}}$. The quotient by
the descended nilpotent ideal agrees with the reduction on
these opens, because a smooth algebra over a field is reduced.
Thus $(X_{K'})_{\mathrm{red}}$ has the desired dense smooth open.

Choose an affine open $S=\operatorname{Spec}A$, and generators
$a_1,\ldots,a_s$ of $K'/K$ with $a_i^{p^e}\in K$
for one common $e$. Invert the denominators of these powers.
Then $A'=A[a_1,\ldots,a_s]\subset K'$ is finite over $A$.
The equations $T_i^{p^e}-a_i^{p^e}$ show that each geometric
fiber has at most one point; integrality gives a point in every
fiber. Hence $\operatorname{Spec}A'\to\operatorname{Spec}A$
is finite, surjective and radicial. Spread the finitely presented
generic smooth neighborhoods by clearing their denominators.
Remove the closures in $S$ of the images of any remaining
vertical irreducible components of $Y$. These images have nondense
closures, so this removes no generic point of $S$; and because
$S'\to S$ is a homeomorphism on underlying spaces it removes no
generic point of $S'$ either. Write $S_1\subseteq S$ for the
surviving open and $S'_1=S'\times_SS_1$, so that
$S'_1\to S_1$ is again finite, surjective and radicial, and still a
homeomorphism on underlying spaces; the shrinking is therefore
performed on the base, and the descent step below may use it. The
resulting smooth open is dense in $(X_{S'_1})_{\mathrm{red}}$.

At each of its finitely many generic points the constructible
stratification of [def-weil-pbc-constructible-complexes]
supplies an open neighborhood on which $F$ is locally constant.
Intersect with their union. The complement contains no generic
point of any component of the generic fiber. A proper closed
subset of an irreducible finite-type scheme over a field has
strictly smaller dimension, which proves the last assertion.
