import Verso
import VersoManual
import VersoBlueprint
import WeilConjectures
import WeilConjecturesBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Zeta functions" =>

The arithmetic objects of the final statements: point counts, the zeta
series, the Euler product over closed points, integrality, the executable
normalization tests, and the three statement-level predicates on integer
polynomials. This chapter is the best-formalized part of the project: most
nodes link to sorry-free declarations in the repository.

:::group "grp-zeta"
The zeta function of a variety over a finite field and the statement-level
predicates of the Weil conjectures.
:::

# Point counts

:::definition "Z-point-count" (parent := "grp-zeta") (lean := "AlgebraicGeometry.Scheme.Hom.pointCount") (tags := "existing-project")
For a scheme $`X` over $`k` (structure morphism
$`f \colon X \to \Spec k`) and $`n \geq 1`, the point count
$`N_n := \# X(k_n)` where $`k_n` is the degree-$`n` extension of $`k`
(realized as the splitting field of $`x^{q^n} - x`): the number of
morphisms $`\Spec k_n \to X` over $`\Spec k`, with junk value $`0` when
infinite. Formalized as `pointCount` via `fieldPoints`.
:::

:::lemma_ "Z-point-count-finite" (parent := "grp-zeta") (uses := "Z-point-count") (lean := "AlgebraicGeometry.Scheme.Hom.finite_fieldPoints") (tags := "existing-project")
For $`f` quasi-compact and locally of finite type over a finite field,
$`X(K)` is finite for every finite extension $`K/k`, so `pointCount`
counts an actual finite set. Formalized and sorry-free
(`finite_fieldPoints`).
:::

:::theorem "Z-closed-points" (parent := "grp-zeta") (uses := "Z-point-count") (lean := "AlgebraicGeometry.Scheme.Hom.pointCount_eq_sum") (tags := "existing-project")
Point-counting via closed points: for $`f` quasi-compact, locally of
finite type, and $`n \neq 0`,
$$`N_n = \sum_{\deg x \mid n} \deg x,`
the sum over the (finitely many) closed points of $`X` whose residue
degree $`\deg x = [\kappa(x) : k]` divides $`n`. Formalized and sorry-free
as `pointCount_eq_sum`. Mathematically: a $`k_n`-point is a closed point
$`x` with $`\deg x \mid n` together with a $`k`-embedding
$`\kappa(x) \hookrightarrow k_n`, of which there are exactly $`\deg x`;
this is the grouping of geometric points into Frobenius orbits, and it is
the arithmetic shadow of "fixed points of $`F^n` = $`k_n`-points" used in
the trace formula ({bpref "TR-frobenius-fixed-points"}[]).
:::

# The zeta series

:::definition "Z-zeta-series" (parent := "grp-zeta") (uses := "Z-point-count, ML-power-series-exp") (lean := "AlgebraicGeometry.Scheme.Hom.zetaSeries") (tags := "existing-project")
The zeta function of $`X/k` as a *formal* power series:
$$`Z(X, t) = \exp\Bigl(\sum_{n \geq 1} N_n \frac{t^n}{n}\Bigr) \in \QQ[\![t]\!],`
formalized as `zetaSeries` by substituting into `PowerSeries.exp`. It has
constant coefficient $`1` (`constantCoeff_zetaSeries`, sorry-free). It is
related to the Dirichlet-type zeta of $`X` as an abstract scheme by
$`\zeta_X(s) = Z(X, q^{-s})`, but the analytic object plays no role in
the main chain.
:::

:::lemma_ "Z-log-derivative" (parent := "grp-zeta") (uses := "Z-zeta-series") (lean := "AlgebraicGeometry.Scheme.Hom.X_mul_derivative_zetaSeries") (tags := "existing-project")
The logarithmic-derivative characterization:
$$`t \cdot Z'(X, t) = \Bigl(\sum_{n \geq 1} N_n t^n\Bigr) \cdot Z(X, t),`
formalized and sorry-free as `X_mul_derivative_zetaSeries`. Together with
$`Z(0) = 1` this *uniquely determines* $`Z` (coefficient recursion), and
it is the device by which the repository proves Euler-product-type
identities without a logarithm API — the same device that
{bpref "LA-exp-log-iso"}[] will package as a group isomorphism.
:::

:::theorem "Z-euler-product" (parent := "grp-zeta") (uses := "Z-zeta-series, Z-closed-points") (lean := "AlgebraicGeometry.Scheme.Hom.zetaSeries_eq_tprod") (tags := "existing-project")
The Euler product: for $`f` quasi-compact and locally of finite type,
$$`Z(X, t) = \prod_{x \in |X|_{\mathrm{cl}}} \frac{1}{1 - t^{\deg x}},`
the product over closed points, converging coefficientwise (for each $`N`
only the finitely many $`x` with $`\deg x \leq N` contribute below
$`t^{N+1}`). Formalized and sorry-free as `zetaSeries_eq_tprod` using the
coefficientwise (`WithPiTopology`) infinite product.
:::

:::theorem "Z-integrality" (parent := "grp-zeta") (uses := "Z-zeta-series") (tags := "elementary-missing") (effort := "small") (priority := "high")
Integrality of the zeta series: $`Z(X, t) \in 1 + t\,\ZZ[\![t]\!]`; that
is, every coefficient of the a priori rational power series is a
non-negative integer.
:::

:::proof "Z-integrality" (uses := "Z-euler-product, LA-locally-finite-products")
Each Euler factor $`(1 - t^{d})^{-1} = \sum_{m \geq 0} t^{dm}` lies in
$`1 + t\,\mathbb{N}[\![t]\!]`; by {bpref "Z-euler-product"}[] the zeta
series is the coefficientwise product of these factors, and each
coefficient of the product is a *finite* sum of products of natural
numbers ({bpref "LA-locally-finite-products"}[]) — hence a natural
number. Alternatively and equivalently, the coefficient of $`t^N` counts
effective zero-cycles of degree $`N` on $`X`. This node is the input
"$`Z \in \ZZ[\![t]\!]`" of the integral Fatou lemma; without it the final
polynomials could not be taken integral.
:::

:::lemma_ "Z-normalization-tests" (parent := "grp-zeta") (uses := "Z-zeta-series") (tags := "elementary-missing") (effort := "small")
Executable convention tests:
$$`Z(\Spec k, t) = \frac{1}{1-t}, \quad Z(\mathbb{A}^1_k, t) = \frac{1}{1-qt}, \quad Z(\mathbb{P}^1_k, t) = \frac{1}{(1-t)(1-qt)}.`
These pin every sign and twist convention of the project: comparing with
the cohomological factorization forces geometric Frobenius to act by
$`1` on $`H^0`, by $`q` on $`H^2(\mathbb{P}^1)` — hence by $`q^{-1}` on
$`\Ql(1)` — and rules out the arithmetic-Frobenius convention, under
which the same tests would produce reciprocal eigenvalues.
:::

:::proof "Z-normalization-tests"
Point counts: $`\#(\Spec k)(k_n) = 1`, $`\#\mathbb{A}^1(k_n) = q^n`,
$`\#\mathbb{P}^1(k_n) = q^n + 1`. Then
$`\exp(\sum t^n/n) = (1-t)^{-1}`,
$`\exp(\sum q^n t^n/n) = (1-qt)^{-1}`, and the third is the product of
the first two ($`\exp` of the sum). Formalization route: compute the
point counts from the functor of points (for $`\mathbb{A}^1`,
$`X(k_n) = k_n`; for $`\mathbb{P}^1`, homogeneous coordinates), then
apply the logarithmic-derivative uniqueness
({bpref "Z-log-derivative"}[]) to identify the closed forms.
:::

# The statement-level predicates

The three conclusions are expressed as predicates on a family
$`P \colon \operatorname{Fin}(2d+1) \to \ZZ[t]`, keeping all cohomology
out of the final statements.

:::definition "Z-weil-factorization" (parent := "grp-zeta") (uses := "Z-zeta-series") (lean := "AlgebraicGeometry.IsWeilFactorization") (tags := "existing-project")
`IsWeilFactorization q d Z P`: (i) every $`P_i` has constant coefficient
$`1`; (ii) $`P_0 = 1 - t`; (iii) $`P_{2d} = 1 - q^d t`; (iv)
$$`Z \cdot \prod_{i \text{ even}} P_i = \prod_{i \text{ odd}} P_i \quad \text{in } \QQ[\![t]\!].`
This is $`Z = (P_1 \cdots P_{2d-1})/(P_0 \cdots P_{2d})` stated without
dividing power series.
:::

:::definition "Z-fe-predicate" (parent := "grp-zeta") (lean := "AlgebraicGeometry.WeilFunctionalEquation") (tags := "existing-project")
`WeilFunctionalEquation q d P`: for every $`i`, the multiset of complex
roots of $`P_{2d-i}` equals the image of the multiset of complex roots of
$`P_i` under $`z \mapsto (q^d z)^{-1}`. Equivalently
$`\alpha \mapsto q^d/\alpha` matches reciprocal roots with multiplicity.
This root-multiset form is stronger than (and implies) the classical
identity $`Z(X, 1/(q^d t)) = \pm q^{d\chi/2} t^\chi Z(X, t)`; the sign
analysis lives in {bpref "DU-sign-analysis"}[] and the derivation of the
classical form in {bpref "W-functional-equation"}[].
:::

:::definition "Z-rh-predicate" (parent := "grp-zeta") (lean := "AlgebraicGeometry.WeilRiemannHypothesis") (tags := "existing-project")
`WeilRiemannHypothesis q d P`: every complex root $`z` of the image of
$`P_i` in $`\CC[t]` satisfies $`\|z\| = q^{-i/2}`. Because $`P_i` has
integer coefficients and constant coefficient $`1`, its reversal
$`t^{\deg P_i} P_i(1/t)` is monic integral, so all reciprocal roots are
automatically algebraic integers; the predicate constrains all their
complex absolute values to $`q^{i/2}` — the classical "all conjugates"
form of the Riemann hypothesis.
:::
