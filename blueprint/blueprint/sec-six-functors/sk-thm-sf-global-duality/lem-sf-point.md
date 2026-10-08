+++
id = "lem-sf-point"
kind = "lemma"
title = "The point, evaluated"
order = 2180
uses = ["def-sf-datum", "def-weil-finite-coefficient-point", "def-weil-ordinary-compact-cohomology"]
+++
In the setting of [def-sf-datum], let $s=\operatorname{Spec}k$ with
structure morphism $a_s=\operatorname{id}_s$. Then
$\omega_s=Ra_s^!\Lambda\cong\Lambda_s$; for every object $C$ of the
point category one has
$R\mathcal H om_s(C,\omega_s)\cong R\operatorname{Hom}_\Lambda(C,\Lambda)$;
evaluation at the geometric point is an exact equivalence
$\Fib_s:D^b_c(s,\Lambda)\to D^b_{\mathrm{fin}}(A_{E,n})$, hence
conservative; and for $K\in D^b_{ctf}(X,\Lambda)$ one has
$\Fib_s(Ra_{X!}K)=R\Gamma_c(X,K)$,
$\Fib_s(Ra_{X*}K)=R\Gamma(X,K)$ and
$H^r(-)=\operatorname{Hom}_s(\Lambda[-r],-)$.

## Proof

The operations are those of the six-functor datum of [def-sf-datum].
$Rf^!$ is the right adjoint of $Rf_!$ by (A1); for $f=\operatorname{id}_s$
the identity functor is its own right adjoint, so
$Ra_s^!\Lambda\cong\Lambda_s$. The identification of
$R\mathcal H om_s$ with $R\operatorname{Hom}_\Lambda$ is
[def-weil-finite-coefficient-point]. The two identifications of the
global-section complexes are the definitions of
[def-weil-ordinary-compact-cohomology], and the last display is the
shift convention together with $\operatorname{Hom}_s(\Lambda,-)=\Fib_s$.
Conservativity and exactness hold because $\Fib_s$ is an equivalence.
