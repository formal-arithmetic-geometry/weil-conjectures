/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Verso
import VersoManual
import VersoBlueprint
import WeilConjectures.Statement

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option linter.hashCommand false
set_option linter.style.longLine false

#doc (Manual) "Statement" =>

Throughout, $`k` is a finite field with $`q` elements and $`X` is a scheme over $`k`,
given by a structure morphism $`f \colon X \to \operatorname{Spec} k`.

:::group "weil_statement"
The statement of the Weil conjectures.
:::

:::definition "point_count" (parent := "weil_statement") (lean := "AlgebraicGeometry.Scheme.Hom.pointCount")
For $`n \ge 1`, the point count $`N_n` is the number of points of $`X` rational over
the degree $`n` extension $`\mathbf{F}_{q^n}` of $`k`, that is, the number of morphisms
$`\operatorname{Spec} \mathbf{F}_{q^n} \to X` over $`k`. For $`X` of finite type over
$`k` this number is finite.
:::

:::definition "zeta_function" (parent := "weil_statement") (lean := "AlgebraicGeometry.Scheme.Hom.zetaSeries")
The zeta function of $`X` over $`k` is the formal power series
$`Z(X, t) = \exp\bigl(\sum_{n \ge 1} N_n t^n / n\bigr) \in \mathbf{Q}[\![t]\!]`,
where $`N_n` is the point count of {uses "point_count"}[]. It is related to the zeta
function $`\zeta_X` of $`X` as an abstract scheme by $`\zeta_X(s) = Z(X, q^{-s})`.
:::

:::definition "weil_factorization" (parent := "weil_statement") (lean := "AlgebraicGeometry.IsWeilFactorization")
A Weil factorization of a power series $`Z` (for parameters $`q` and $`d`) is a family
of polynomials $`P_0, \dots, P_{2d} \in \mathbf{Z}[t]` with $`P_i(0) = 1`,
$`P_0 = 1 - t` and $`P_{2d} = 1 - q^d t`, such that
$`Z = \frac{P_1 \cdots P_{2d-1}}{P_0 \cdots P_{2d}}`, i.e. $`Z \cdot \prod_{i \text{ even}} P_i = \prod_{i \text{ odd}} P_i`
as power series. This is the shape predicted for the zeta function
({uses "zeta_function"}[]) of a smooth, proper, geometrically integral scheme of
dimension $`d`.
:::

:::definition "functional_equation" (parent := "weil_statement") (lean := "AlgebraicGeometry.WeilFunctionalEquation")
A family $`P_0, \dots, P_{2d}` satisfies the Weil functional equation if
$`\alpha \mapsto q^d / \alpha` maps the inverse roots of $`P_i` bijectively (with
multiplicity) onto the inverse roots of $`P_{2d-i}`; in terms of the complex root
multisets, $`z \mapsto 1 / (q^d z)` identifies the roots of $`P_i` with those of
$`P_{2d-i}`. For the associated rational function this implies the classical form
$`Z(X, 1/(q^d t)) = \pm\, q^{d\chi/2}\, t^{\chi}\, Z(X, t)` with
$`\chi = \sum_i (-1)^i \deg P_i`.
:::

:::definition "riemann_hypothesis" (parent := "weil_statement") (lean := "AlgebraicGeometry.WeilRiemannHypothesis")
A family $`P_0, \dots, P_{2d}` satisfies the Weil Riemann hypothesis if every inverse
root of $`P_i` has absolute value $`q^{i/2}`, i.e. every complex root $`z` of $`P_i`
satisfies $`\lVert z \rVert = q^{-i/2}`.
:::

:::theorem "rationality" (parent := "weil_statement") (lean := "AlgebraicGeometry.Scheme.zetaSeries_rational")
*Dwork's theorem.* For $`X` of finite type over $`k`, the zeta function
({uses "zeta_function"}[]) is a rational function with integer coefficients: there are
polynomials $`P, Q \in \mathbf{Z}[t]` with $`Q(0) = 1` and $`Z(X, t) \cdot Q = P` in
$`\mathbf{Q}[\![t]\!]`. This is the first Weil conjecture; it holds without any
smoothness or properness hypotheses.
:::

:::theorem "weil_conjectures" (parent := "weil_statement") (lean := "AlgebraicGeometry.Scheme.weil_conjectures")
*The Weil conjectures* (Dwork, Grothendieck, Deligne). Let $`X` be a smooth, proper,
geometrically integral scheme of dimension $`d` over $`k`. Then there exists a family
of polynomials $`P_0, \dots, P_{2d} \in \mathbf{Z}[t]` which is a Weil factorization of
$`Z(X, t)` ({uses "weil_factorization"}[]) and satisfies the functional equation
({uses "functional_equation"}[]) and the Riemann hypothesis
({uses "riemann_hypothesis"}[]).
:::
