import Verso
import VersoManual
import VersoBlueprint
import WeilConjecturesBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The trace formula" =>

The trace formula converts point counts into alternating sums of traces of
geometric Frobenius and thereby feeds the entire algebraic machine. This
chapter records the two interface statements (AX1) consumed by the final
assembly, and the full realization chain: supertrace calculus, the
Lefschetz–Verdier trace formula with finite coefficients, Frobenius local
terms, the fixed-point identification, the closed-point conversion, and
the cohomological L-function formula (which the purity branch also
consumes).

:::group "grp-trace"
The Grothendieck–Lefschetz trace formula: interface statements and
realization chain.
:::

# Interface statements

:::theorem "TR-interface-proper" (parent := "grp-trace") (uses := "Z-point-count, LA-frobenius-module, LA-trace-iter") (tags := "temporary-axiom, deep-input") (effort := "large") (priority := "high")
Trace formula, smooth projective form (interface hypothesis AX1). Let
$`X` be smooth and projective over $`k = \Fq`, of pure dimension $`d`,
and $`K` an algebraically closed field of characteristic $`0` (realized
as $`\Qlbar`). There exist finite-dimensional $`K`-vector spaces
$`H^0, \dots, H^{2d}` with automorphisms $`F_i` (geometric Frobenius)
such that for all $`n \geq 1`
$$`\bigl(\#X(\Fqn{n}) : K\bigr) = \sum_{i=0}^{2d} (-1)^i\, \Tr\bigl(F_i^n \mid H^i\bigr).`
The sum is finite by fiat (the family is indexed by
$`0 \leq i \leq 2d`); each trace is the trace of an endomorphism of a
finite-dimensional space. For proper smooth $`X` ordinary and
compactly-supported cohomology agree ({bpref "SIX-proper-comparison"}[]),
which is why no compact-support decoration appears here.
:::

:::proof "TR-interface-proper" (uses := "TR-l-function, SIX-proper-comparison, ET-adic-formalism")
Interface axiom until the realization chain is formalized. Realization:
specialize the cohomological L-function formula
({bpref "TR-l-function"}[]) to the constant sheaf $`\Ql` on $`X_0 = X`,
take logarithmic derivatives of both sides, and compare coefficients:
the local factor at a closed point $`x` contributes
$`\deg x \cdot \Tr(F_x^{n/\deg x})` to the coefficient of $`t^n` (when
$`\deg x \mid n`), which sums to $`N_n` by the closed-point conversion
({bpref "TR-closed-points-conversion"}[]); the global side contributes
the alternating trace sum. Identify $`H_c = H` by properness
({bpref "SIX-proper-comparison"}[]) and pass from finite to $`\Qlbar`
coefficients by the adic formalism ({bpref "ET-adic-formalism"}[]).
Boundedness of the range by $`2d` is the cohomological-dimension bound
({bpref "SIX-rf-shriek"}[]).
:::

:::theorem "TR-interface-cc" (parent := "grp-trace") (uses := "Z-point-count, LA-frobenius-module, LA-trace-iter") (tags := "temporary-axiom, deep-input") (effort := "large")
Trace formula, compactly-supported form (interface hypothesis AX1′). For
*any* separated scheme $`X` of finite type over $`k` there are
finite-dimensional $`K`-spaces $`H_c^0, \dots, H_c^{2\dim X}` with
automorphisms $`F_i` such that
$`(\#X(\Fqn{n}) : K) = \sum_i (-1)^i \Tr(F_i^n \mid H_c^i)` for all
$`n \geq 1`. This weaker-hypothesis variant feeds the unconditional
rationality theorem {bpref "W-rationality"}[]; no smoothness,
properness, or connectedness is assumed.
:::

:::proof "TR-interface-cc" (uses := "TR-l-function, ET-adic-formalism")
Same specialization of {bpref "TR-l-function"}[] as in the proper case,
without the $`H_c = H` identification; the spaces are
$`H_c^i(X_{\Fqbar}, \Ql) \otimes \Qlbar`, finite-dimensional by
{bpref "GEO-finiteness"}[] with vanishing above $`2 \dim X` by
{bpref "SIX-rf-shriek"}[].
:::

# Elementary calculus

:::lemma_ "TR-supertrace" (parent := "grp-trace") (uses := "LA-trace-iter, LA-charpoly-rev") (tags := "elementary-missing") (effort := "medium")
Supertrace calculus for bounded complexes: for a bounded complex $`C` of
finite-dimensional vector spaces with an endomorphism $`u`, the
supertrace $`\Tr_s(u) := \sum_i (-1)^i \Tr(u \mid C^i)` (i) equals
$`\sum_i (-1)^i \Tr(H^i(u) \mid H^i(C))` (invariance under passing to
cohomology), (ii) is additive in short exact sequences of complexes, and
(iii) satisfies the alternating determinant–trace relation
$`\exp(\sum_n \Tr_s(u^n) t^n/n) = \prod_i \det(1 - t u|_{C^i})^{(-1)^{i+1}}`.
:::

:::proof "TR-supertrace" (uses := "LA-trace-additive, LA-det-trace-graded")
(i): filter each $`C^i` by boundaries and cycles,
$`B^i \subseteq Z^i \subseteq C^i`; $`u` preserves the filtration, trace
is additive on it ({bpref "LA-trace-additive"}[]), and the boundary
contributions cancel in the alternating sum because $`d` induces
$`u`-equivariant isomorphisms $`C^i/Z^i \cong B^{i+1}`. (ii): trace
additivity degreewise. (iii): {bpref "LA-det-trace-graded"}[]. This
node is what lets the realization work with complexes and their
truncations without ever invoking spectral sequences.
:::

:::lemma_ "TR-closed-points-conversion" (parent := "grp-trace") (uses := "Z-closed-points") (tags := "elementary-missing") (effort := "small")
Closed-point/rational-point conversion for traces: let $`x` be a closed
point of $`X_0` of degree $`d_x` and $`F_x` the local geometric
Frobenius acting on a stalk at a geometric point over $`x`. For
$`n \geq 1`, the fixed points of $`F^n` lying over $`x` are nonempty iff
$`d_x \mid n`, in which case there are $`d_x` of them and the operator
induced at each is $`F_x^{n/d_x}`. Hence, for a sheaf with finite trace
data,
$$`\sum_{y \in X_0(\Fqn{n})} \Tr(F^n_y) = \sum_{d_x \mid n} d_x\, \Tr\bigl(F_x^{n/d_x}\bigr).`
:::

:::proof "TR-closed-points-conversion"
The geometric points over $`x` form one orbit of size $`d_x` under the
Galois action (equivalently under $`F`), because
$`\kappa(x) = \Fqn{d_x}` and geometric points over $`x` correspond to
$`k`-embeddings $`\kappa(x) \to \Fqbar`; $`F^n` fixes such an embedding
iff $`q^n`-power fixes $`\kappa(x)`, i.e. $`d_x \mid n`, and then $`F^n`
acts on the stalk at each fixed geometric point through the local
Frobenius power $`F_x^{n/d_x}` (transport along the orbit conjugates the
action, leaving the trace unchanged). The purely point-counting shadow
($`N_n = \sum_{d_x \mid n} d_x`) is already formalized as
{bpref "Z-closed-points"}[]; this node is its stalk-decorated upgrade.
:::

# Deep realization inputs

:::theorem "TR-lefschetz-verdier" (parent := "grp-trace") (uses := "SH-constructible, SIX-rf-shriek") (tags := "deep-input") (effort := "large")
Lefschetz–Verdier trace formula, finite coefficients. Let $`\Lambda =
\ZZ/\ell^\nu\ZZ` ($`\ell \neq p`), $`X` separated of finite type over an
algebraically closed field, $`c = (c_1, c_2) \colon C \to X \times X` a
correspondence with $`c_2` proper, $`K \in D^b_{ctf}(X, \Lambda)` (finite
Tor dimension, constructible cohomology), and
$`u \colon c_2^* K \to R c_1^! K` a cohomological correspondence, with
the fixed-point scheme $`\operatorname{Fix}(c)` proper. Then
$$`\Tr\bigl(R\Gamma_c(u) \mid R\Gamma_c(X, K)\bigr) = \sum_{\beta \in \pi_0(\operatorname{Fix} c)} \operatorname{LT}_\beta(u),`
where the local terms $`\operatorname{LT}_\beta` are defined by
evaluation against the dualizing complex on the fixed-point components.
:::

:::proof "TR-lefschetz-verdier"
Deep input (SGA 5 / Illusie). Internal decomposition planned when this
leaf is attacked: compactification of correspondences; additivity of
trace classes in the localization triangles; proper pushforward and
étale pullback of trace classes; the terminal computation over a point.
The route deliberately avoids permutation-resolution arguments (invalid
when $`\ell` divides the order of the group). For the Weil conjectures
only the Frobenius correspondence is needed, so a first formalization may
restrict the statement to that case
({bpref "TR-frobenius-local-terms"}[]) — but the trace-class calculus is
the same, so the general statement is recorded as the honest leaf.
:::

:::theorem "TR-frobenius-fixed-points" (parent := "grp-trace") (uses := "ET-frobenius-dictionary") (tags := "elementary-missing") (effort := "medium")
Fixed points of Frobenius powers: for $`X_0` separated of finite type
over $`\Fq` with base change $`X = X_0 \times_k \Fqbar`, the fixed-point
scheme of the $`n`-th power of the $`q`-power Frobenius correspondence on
$`X` is finite, reduced (étale over $`\Fqbar`), and its points are
canonically $`X_0(\Fqn{n})`; the graph of $`F^n` is transversal to the
diagonal because $`d(\operatorname{Frob}) = 0` (the differential of the
$`q`-power map is zero in characteristic $`p`, as $`d(s^q) = q s^{q-1} ds
= 0`).
:::

:::proof "TR-frobenius-fixed-points"
On points: a geometric point fixed by $`F^n` is exactly a point with
coordinates in the fixed field of the $`q^n`-power map, i.e. in
$`\Fqn{n}`. Scheme-theoretically, the intersection of the graph
$`\Gamma_{F^n}` with the diagonal $`\Delta` in $`X \times X` has, at each
intersection point, tangent condition
$`\ker(1 - dF^n) = \ker(1 - 0) = 0`, so the intersection is étale over
the base — each fixed point is isolated with multiplicity one. This is
why the *geometric* Frobenius (the $`q`-power correspondence) is the
operator in the trace formula: for a general endomorphism the local term
is not the naive stalk trace, but $`d\operatorname{Frob} = 0` makes it
so ({bpref "TR-frobenius-local-terms"}[]).
:::

:::theorem "TR-frobenius-local-terms" (parent := "grp-trace") (uses := "TR-lefschetz-verdier, TR-frobenius-fixed-points") (tags := "deep-input") (effort := "large")
Frobenius local terms: for the correspondence
$`(\operatorname{id}, F^n)` on $`X` with coefficients
$`K_0 \in D^b_{ctf}(X_0, \Lambda)`, the local term at each fixed point
$`y \in X_0(\Fqn{n})` equals the naive stalk supertrace
$`\Tr_s(F^n_y \mid K_{\bar y})`. Consequently
$$`\Tr_s\bigl(F^n \mid R\Gamma_c(X, K)\bigr) = \sum_{y \in X_0(\Fqn{n})} \Tr_s\bigl(F^n_y \mid K_{\bar y}\bigr).`
:::

:::proof "TR-frobenius-local-terms"
Deep input. The vanishing differential
({bpref "TR-frobenius-fixed-points"}[]) makes each fixed point a
transversal intersection, and for transversal fixed points the
Lefschetz–Verdier local term reduces to the stalk supertrace (SGA 5 III;
the reduction uses the compatibility of local terms with the trace map
of the ambient space at an isolated point). For non-smooth $`X_0`, one
stratifies by smooth pieces over the perfect field $`\Fq` and uses
additivity of both sides in the localization triangles
({bpref "SIX-localization-triangle"}[]) — no resolution of
singularities is needed.
:::

:::theorem "TR-l-function" (parent := "grp-trace") (uses := "SH-weil-sheaf, TR-supertrace") (tags := "deep-input") (effort := "medium")
Cohomological L-function formula (Grothendieck): for a constructible
Weil $`\Qlbar`-sheaf $`\mathcal{F}_0` on a separated finite-type
$`X_0/\Fq` (more generally a bounded complex),
$$`L(X_0, \mathcal{F}_0, t) := \prod_{x \in |X_0|} \det\bigl(1 - t^{\deg x} F_x \mid \mathcal{F}_{\bar x}\bigr)^{-1} = \prod_i \det\bigl(1 - t F \mid H_c^i(X, \mathcal{F})\bigr)^{(-1)^{i+1}},`
an identity in $`1 + t\,\Qlbar[\![t]\!]` (the left side converges
$`t`-adically since only finitely many points have bounded degree).
:::

:::proof "TR-l-function" (uses := "TR-frobenius-local-terms, TR-closed-points-conversion, LA-det-trace-graded, LA-locally-finite-products, ET-adic-formalism")
Take $`\operatorname{logOf}` of both sides and compare coefficients of
$`t^n`. Right side: alternating trace sum
$`\Tr_s(F^n \mid R\Gamma_c)` by {bpref "LA-det-trace-graded"}[]. Left
side: the local factor at $`x` contributes
$`\deg x \cdot \Tr_s(F_x^{n/\deg x})` when $`\deg x \mid n`
({bpref "LA-locally-finite-products"}[] for the locally finite product,
then the one-factor computation); summing over $`x` and applying the
conversion {bpref "TR-closed-points-conversion"}[] gives
$`\sum_{y \in X_0(\Fqn{n})} \Tr_s(F^n_y)`. The two coefficient families
agree by the Frobenius trace formula
({bpref "TR-frobenius-local-terms"}[]), first with finite coefficients,
then for $`\Qlbar` by {bpref "ET-adic-formalism"}[]. This node is
consumed twice: by the interface trace formulas above, and — crucially —
*inside the weight machinery* (the semicontinuity estimate
{bpref "MON-boundary-m1"}[] and the real-sheaf purity criterion
{bpref "PUR-real-purity"}[] are proved by analyzing this identity after
applying $`\iota`).
:::
