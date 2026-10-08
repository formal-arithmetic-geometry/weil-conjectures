+++
id = "rem-trf-verdier-decomposition"
kind = "remark"
title = "Status of the fixed-point trace construction"
order = 2323
uses = ["cor-trf-constant-stalk-trace", "def-trf-dualizing-complex", "lem-trf-trace-map-from-external-duality", "thm-trf-fixed-point-evaluation-finite", "thm-trf-internal-hom-pullback", "thm-trf-verdier-duality"]
+++
The proved internal-Hom comparison
[thm-trf-internal-hom-pullback] requires a site-perfect first
variable. The resulting computation
[thm-trf-fixed-point-evaluation-finite] gives the ordinary stalk
trace $\sigma_{h,K}$; for constant coefficients its value is $1$
by [cor-trf-constant-stalk-trace].

The geometric construction has a different input:
[thm-trf-verdier-duality] asks for external Verdier duality, and
[lem-trf-trace-map-from-external-duality] constructs the genuine
fixed-point trace conditionally on that comparison. The ordinary
tensor dual $K^\vee=R\mathcal Hom_A(K,A_X)$ and the Verdier dual
$D_XK=R\mathcal Hom_A(K,\omega_{X,A})$ of
[def-trf-dualizing-complex] have different targets. In particular,
$R\mathcal Hom_A(K,K)$ must not be identified with
$K\otimes_A^LD_XK$. No identification between $\sigma_{h,K}$
and a Verdier local term has been proved here.
