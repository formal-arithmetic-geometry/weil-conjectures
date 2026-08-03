import Verso
import VersoManual
import VersoBlueprint
import WeilConjecturesBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "The abstract cohomology package" =>

Layer II: the minimal interface between the algebraic core and geometry.
A *Weil package* for a variety bundles exactly the data and four
hypotheses that the final assembly consumes — nothing more. This chapter
also records, explicitly, what is *excluded* from the interface and why.

:::group "grp-package"
The abstract Weil cohomology package and the two theorems that consume
and instantiate it.
:::

# The package

:::definition "COH-weil-package" (parent := "grp-package") (uses := "LA-frobenius-module, Z-point-count") (tags := "infrastructure") (effort := "medium") (priority := "high")
A *Weil package* for $`(q, d, N)` — where $`q \geq 2`, $`d \geq 0`, and
$`N \colon \{n \geq 1\} \to \mathbb{N}` — over an algebraically closed
field $`K` of characteristic $`0` consists of finite-dimensional
$`K`-vector spaces $`H^0, \dots, H^{2d}` with automorphisms $`F_i`, and:
* *(AX1)* trace formula: $`(N_n : K) = \sum_i (-1)^i \Tr(F_i^n)` for
  all $`n \geq 1` ({bpref "TR-interface-proper"}[]);
* *(AX2)* similitude pairings with multiplier $`q^d` and
  $`(-1)^d`-symmetric middle pairing ({bpref "DU-interface"}[]);
* *(AX3)* endpoint: $`\dim H^0 = 1`, $`F_0 = \operatorname{id}`
  ({bpref "DU-endpoint"}[]);
* *(AX4)* universal purity: every eigenvalue of $`F_i` is universally
  pure of weight $`i` relative to $`q`
  ({bpref "COH-purity-input"}[]);
* *(CARD)* $`\#K \leq 2^{\aleph_0}`.
In Lean this is one structure; the four axioms are fields, so that "the
Weil conjectures assuming AX1–AX4" is a theorem about the structure with
no `axiom` declarations anywhere.
:::

:::theorem "COH-purity-input" (parent := "grp-package") (uses := "WT-universal") (tags := "temporary-axiom, deep-input") (priority := "high")
Universal purity (interface hypothesis AX4): in a Weil package, for
every ring homomorphism $`\iota \colon K \to \CC`, every $`i`, and
every eigenvalue $`\alpha` of $`F_i`:
$`\|\iota\alpha\|^2 = q^{i}`. This node *is* the interface form of the
Riemann hypothesis; it is realized by Deligne's purity theorem
({bpref "PUR-smooth-proper"}[]) and is the deepest input of the
project. Note what it does *not* assert: no algebraicity of
$`\alpha` (a conclusion, {bpref "W-algebraicity"}[]), no continuity of
$`\iota`, no preferred embedding.
:::

:::proof "COH-purity-input" (uses := "PUR-smooth-proper")
Temporary axiom; eliminated by the purity branch: for
$`K = \Qlbar` and $`H^i = H^i(X_{\Fqbar}, \Ql) \otimes \Qlbar`, this is
exactly {bpref "PUR-smooth-proper"}[].
:::

# The two theorems

:::theorem "COH-version-i" (parent := "grp-package") (uses := "COH-weil-package, Z-weil-factorization, Z-fe-predicate, Z-rh-predicate") (tags := "elementary-missing") (effort := "medium") (priority := "high")
Layer I main theorem (graded Frobenius linear algebra): let
$`(H, F)` be a Weil package for $`(q, d, N)` and suppose additionally
$`Z := \exp(\sum N_n t^n/n) \in 1 + t\ZZ[\![t]\!]` (automatic for actual
point counts, {bpref "Z-integrality"}[]). Then the polynomials
$`P_i := \det(1 - tF_i)` descend to $`\ZZ[t]` and satisfy
`IsWeilFactorization`, `WeilFunctionalEquation`, and
`WeilRiemannHypothesis` for $`(q, d, Z)`, together with endpoint
computation, explicit functional-equation sign
$`\varepsilon = (-1)^\chi \delta^{(-1)^d}`, algebraicity and
integrality of all reciprocal roots, and uniqueness of the family
$`(P_i)` given $`(Z, q, d)`. *No scheme or sheaf appears in statement
or proof.*
:::

:::proof "COH-version-i" (uses := "W-factorization, W-rationality-reduced, W-endpoints, W-functional-equation, W-no-cancellation, W-factor-identification, W-algebraicity, W-rational-coefficients, W-integral-coefficients, W-riemann-hypothesis, W-ell-independence")
This is the bundled restatement of the final-assembly chain; the proof
is the composition of the eleven listed nodes in that order. The node
exists so that Layer I is *one* checkable Lean theorem whose hypotheses
are exactly the package fields — the formal analogue of the lecture
notes' "elementary Frobenius-module theorem".
:::

:::theorem "COH-instantiation" (parent := "grp-package") (uses := "COH-weil-package") (tags := "temporary-axiom") (effort := "medium") (priority := "high")
Layer II instantiation: for every smooth, projective, geometrically
integral $`X` of pure dimension $`d` over $`\Fq`, there exists a Weil
package for $`(q, d, N_\bullet(X))` over $`K = \Qlbar`. Until Layer III
is formalized this theorem is the *axiom boundary*: it is exactly the
conjunction AX1 ∧ AX2 ∧ AX3 ∧ AX4 ∧ CARD for the étale realization,
and the axiom-audit of the conditional Weil theorem reports precisely
these four mathematical debts (CARD is discharged by
{bpref "LA-qlbar-cardinality"}[] from the start).
:::

:::proof "COH-instantiation" (uses := "ET-realization, LA-qlbar-cardinality")
Realized by {bpref "ET-realization"}[]: étale cohomology supplies the
spaces and operators, the trace-formula chapter discharges AX1, the
duality chapter AX2–AX3, the purity branch AX4, and
{bpref "LA-qlbar-cardinality"}[] the cardinality bound.
:::

# What the interface excludes, and why

Each standard Weil-cohomology property *absent* from
{bpref "COH-weil-package"}[] is absent because no downstream node uses
it. The list, with the reason it is not needed:

* *Functoriality in $`X`* — the final theorem is about a single $`X`;
  no morphism between varieties is ever applied to cohomology.
* *Künneth formula* — the only product situations (Fourier kernel
  manipulations) are handled by the projection formula
  ({bpref "SIX-projection-formula"}[]) inside the realization layer.
* *Cycle classes and intersection theory* — the trace formula is taken
  as an interface input, not derived from a cycle-class computation of
  the diagonal.
* *Cup products* — only the middle-pairing *sign* survives into AX2;
  the ring structure itself is invisible to the algebra.
* *Weak and hard Lefschetz* — the Weil I induction is replaced by the
  Fourier-transform route; no hyperplane sections appear on the
  critical path.
* *Weight filtrations and mixedness structures* — at package level,
  purity is an eigenvalue statement; filtrations appear only inside the
  realization ({bpref "WT-sheaf-mixed"}[]).
* *Independence-of-$`\ell` comparison isomorphisms* — uniqueness of the
  $`P_i` is proved arithmetically ({bpref "W-ell-independence"}[]),
  needing no comparison between different $`\ell`.

This minimality is what makes Layer I formalizable *now*, before any
étale machinery exists in Mathlib.
