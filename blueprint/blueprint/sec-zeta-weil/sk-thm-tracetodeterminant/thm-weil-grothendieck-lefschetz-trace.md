+++
id = "thm-weil-grothendieck-lefschetz-trace"
kind = "theorem"
title = "Grothendieck–Lefschetz trace formula"
order = 2880
uses = ["cor-trf-point-counting", "def-trf-frobenius-operators", "def-trf-karoubi-trace", "def-weil-algebraically-closed-coefficients", "def-weil-derived-cohomology-sheaves", "def-weil-derived-pullback-tensor-hom", "def-weil-finite-field-fiber", "def-weil-frobenius-detailed", "def-weil-global-geometric-frobenius", "def-weil-local-frobenius-trace", "def-weil-ordinary-compact-cohomology", "def-weil-pbc-proetale-site", "def-weil-point-counts-zeta", "def-weil-scheme-morphism-properties", "def-weil-weil-sheaf-complex", "prop-trf-karoubi-independence", "prop-weil-proper-compact-coincidence", "thm-trf-frobenius-fixed-points", "thm-trf-frobenius-local-term", "thm-trf-grothendieck-lefschetz-finite-ring", "thm-trf-grothendieck-lefschetz-qbar", "thm-trf-lefschetz-verdier", "thm-trf-trace-formula-e", "thm-zl-lefschetz-weil-identity"]
+++
Fix the finite-field datum
$p,a,q,k_0,k$, where $q=p^a$, and choose a prime $\ell\neq p$;
write $\Ql=\mathbf Q_\ell$, choose an algebraic closure $\Qlb$ of
$\Ql$, and let $Y_0$ be a
separated finite-type
$k_0$-scheme and put $Y=Y_0\times_{k_0}k$. Let
$K\in D^b_{c,\mathrm W}(Y,\Qlb)$ be a
Weil complex; choose a finite
extension $E/\Ql$ contained in $\Qlb$ and a model
$K_E\in D^b_{c,\mathrm W}(Y,E)$ with scalar extension
$K_E\otimes_E\Qlb=K$. These coefficients are formed on the
small pro-etale site, and the
common-stage
coefficient construction supplies the scalar extension. Use the
geometric Frobenius convention; the induced
cohomological action $F$ is the
global geometric-Frobenius
action. Use the
local Frobenius operators and the
compact-support cohomology
defined for this complex.
For every integer $n\geq1$ and each point
$x\in Y_0(\mathbf F_{q^n})$, choose a
geometric point
$\bar x\to Y$ over $x$, iterate its local Weil isomorphism $n$ times,
and write $K_{E,\bar x}= L\bar x^*\operatorname{For}(K_E)$, using the
derived pullback. The trace
identity is
understood after mapping the left-hand $E$-valued traces to $\Qlb$ along
the chosen inclusion $E\hookrightarrow\Qlb$, and is explicitly

$$
\sum_{x\in Y_0(\mathbf F_{q^n})}\sum_{j\in\mathbf Z}(-1)^j
\Tr\bigl(F_x^{(n)}\mid
\mathcal H^j(\operatorname{For}K_E)_{\bar x}\bigr)
=
\sum_{i\in\mathbf Z}(-1)^i\Tr(F^n\mid H_c^i(Y,K)).
$$

For $K_E=E_Y$, so that $K=(\Qlb)_Y$, and
proper $Y_0$, the
point-count convention specializes to

$$
\#Y_0(\mathbf F_{q^n})
=\sum_{i\in\mathbf Z}(-1)^i\Tr(F^n\mid H^i(Y,\Qlb)).
$$

Here $F_x^{(n)}$ and $K_{\bar x}$ are the
local Frobenius and stalk
constructions, and $H_c^i$ is
compact-support cohomology.

## Proof

*Step 1: the identity.* The local data of the interface are the
local Frobenius operators $F_x^{(n)}$ and the stalk complexes
$K_{\bar x}=L\bar x^*\operatorname{For}(K_E)$ of
[def-weil-local-frobenius-trace], computed with the derived
pullback of [def-weil-derived-pullback-tensor-hom] and traced
alternately over the cohomology sheaves of
[def-weil-derived-cohomology-sheaves]; the
global side is the compact-support cohomology of
[def-weil-ordinary-compact-cohomology] with the geometric-Frobenius
operator of [def-weil-global-geometric-frobenius]. The identity
is the trace formula of the trace-formula chapter: at the finite coefficient stage
it is [thm-trf-grothendieck-lefschetz-finite-ring] (whose finite
ring, finite field, and trace-class hypotheses are the ones recorded in
the interface), the $E$-valued form is [thm-trf-trace-formula-e],
and the $\Qlb$-form over the common-stage coefficients of
[def-weil-algebraically-closed-coefficients] is
[thm-trf-grothendieck-lefschetz-qbar]; the local terms are the
fixed-point and local-term computations of
[thm-trf-frobenius-fixed-points] and
[thm-trf-frobenius-local-term] through the
[thm-trf-lefschetz-verdier] comparison on the projective line, in the
trace-formula chapter's reduction to curves (affine line, Weil
$!$-pushforward along the relative Frobenius, localization),
with the trace classes of
[def-trf-karoubi-trace] and the independence of
[prop-trf-karoubi-independence]. This step inherits the inputs of
the finite-ring trace formula, the construction of the Verdier local trace
and its compatibility with extension by zero to the projective line, both
of which are proved in the trace-formula chapter.
The properness hypothesis in the Lefschetz–Verdier comparison cannot be
dropped for an arbitrary correspondence on a non-proper scheme.
The displayed identity,
understood after the mapping of the $E$-valued traces along
$E\hookrightarrow\Qlb$, is exactly the one of
[thm-trf-grothendieck-lefschetz-qbar] transcribed to the
interface's notation, and the induced Frobenius operators on the
geometric stalks are those of the local Frobenius construction
[def-trf-frobenius-operators].

*Step 2: the point-count specialization.* For
$K_E=E_Y$, $K=(\Qlb)_Y$, and proper $Y_0$, the
interface's constant-sheaf clause is [cor-trf-point-counting],
whose second form replaces compact-support by ordinary cohomology via
the proper coincidence of [prop-weil-proper-compact-coincidence];
the point-count convention is the one of
[def-weil-point-counts-zeta].

*Step 3: the determinant form.* In the smooth-proper
geometrically connected case the same trace formula is the input of
the trace-to-determinant identity [thm-zl-lefschetz-weil-identity]
of the zeta chapter, which converts the per-iterate point counts into the
determinant factorization of the zeta series; this is the form used
in the final theorem's trace-to-determinant step.
