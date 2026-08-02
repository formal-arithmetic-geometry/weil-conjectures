import Verso
import VersoManual
import VersoBlueprint
import WeilConjecturesBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Overview" =>

This blueprint is the complete reverse-engineered proof architecture for a
Lean 4 formalization of the *Weil conjectures*. It starts from the final
theorem — already stated and `sorry`-free in its *statement* in the
repository — and works backwards until every leaf is verified Mathlib
infrastructure, an elementary result that can be formalized directly, a
precisely specified new construction, or a precisely stated deep theorem.

# The target

Let $`X` be a smooth, projective, geometrically integral scheme of pure
dimension $`d` over a finite field $`k` with $`q` elements. The zeta
function
$`Z(X, t) = \exp\bigl(\sum_{n \geq 1} N_n t^n/n\bigr)`, with
$`N_n = \#X(\Fqn{n})`, satisfies: there are polynomials
$`P_0, \dots, P_{2d} \in \ZZ[t]` with constant coefficient $`1`, endpoints
$`P_0 = 1 - t` and $`P_{2d} = 1 - q^d t`, such that
$`Z = (P_1 \cdots P_{2d-1})/(P_0 \cdots P_{2d})` (rationality with
cohomological factorization), the map $`\alpha \mapsto q^d/\alpha` matches
reciprocal roots of $`P_i` and $`P_{2d-i}` with multiplicity (functional
equation), and every complex root $`z` of $`P_i` has $`\|z\| = q^{-i/2}`
(Riemann hypothesis). The reciprocal roots are algebraic integers, and the
family $`(P_i)` is uniquely determined by $`(Z, q, d)` — in particular
independent of every auxiliary choice made in the proof, notably the
prime $`\ell`. The final package is split into separate nodes
({bpref "W-factorization"}[], {bpref "W-rationality"}[],
{bpref "Z-integrality"}[], {bpref "W-functional-equation"}[],
{bpref "W-riemann-hypothesis"}[], {bpref "W-algebraicity"}[],
{bpref "W-ell-independence"}[], {bpref "W-weil-conjectures"}[]); none of
these is an opaque combined node.

# Conventions (fixed once, used by every node)

* $`q = p^r` with $`p` prime; $`k = \Fq`; $`\Fqbar` a fixed algebraic
  closure; $`k_n = \Fqn{n}` the degree-$`n` subextension.
* $`\ell` is a prime $`\neq p`. Coefficients of cohomology are
  $`\Ql` unless another coefficient object is explicitly introduced;
  eigenvalue analysis happens after the flat extension to $`\Qlbar`, and
  the abstract layers use an arbitrary algebraically closed field $`K` of
  characteristic $`0` with $`\#K \leq 2^{\aleph_0}`.
* *Frobenius.* The arithmetic Frobenius is the field substitution
  $`\varphi \colon a \mapsto a^q`, a topological generator of
  $`\operatorname{Gal}(\Fqbar/\Fq)`. The *geometric Frobenius* is
  $`F = \varphi^{-1}`. *Every Frobenius operator acting on cohomology in
  this blueprint is geometric Frobenius*, concretely induced by the
  $`q`-power scheme endomorphism (see {bpref "ET-frobenius-dictionary"}[]);
  the eigenvalues of arithmetic Frobenius are the inverses of ours.
* *Zeta variable.* $`t` is a formal variable: $`Z(X,t)` is an element of
  `PowerSeries ℚ`, defined by the formal exponential. No analytic
  convergence enters anywhere in the main chain.
* *Tate twists.* $`\Ql(1) = (\varprojlim_n \mu_{\ell^n}) \otimes_{\ZZ_\ell} \Ql`;
  geometric Frobenius acts on $`\Ql(1)` by the scalar $`q^{-1}` and on
  $`\Ql(-1)` by $`q`. Twisting by $`(m)` multiplies Frobenius eigenvalues
  by $`q^{-m}`. The conventions are pinned by executable tests
  ({bpref "Z-normalization-tests"}[]): $`Z(\Spec k) = (1-t)^{-1}`,
  $`Z(\mathbb{A}^1) = (1-qt)^{-1}`, $`Z(\mathbb{P}^1) = ((1-t)(1-qt))^{-1}`.
* *Weights.* An element $`\alpha \in K^\times` is $`\iota`-pure of weight
  $`w \in \ZZ` relative to $`q^n` if $`\|\iota\alpha\|^2 = q^{nw}` — the
  *squared* normalization, avoiding square roots and half-integer
  exponents. The weight of $`\Ql(m)` is $`-2m`. Purity statements are
  quantified over *all* ring homomorphisms $`\iota \colon K \to \CC`; no
  topology on $`K` is ever used.

# The proof route

The mathematical route follows the lecture notes accompanying this project:
the Laumon–Deligne approach to Weil II. Its shape:

1. a *geometry-free algebraic core* (trace data $`\Rightarrow`
   factorization; Hankel/Fatou/Gauss $`\Rightarrow` rationality over
   $`\ZZ`; similitude pairings $`\Rightarrow` functional equation with an
   explicit sign analysis; universal $`\iota`-purity $`\Rightarrow`
   Riemann hypothesis, algebraicity, integrality, and
   $`\ell`-independence);
2. purity for smooth proper varieties obtained as a *duality squeeze*: a
   general weight *upper bound* for $`R^i f_!` of mixed sheaves
   (Deligne–Laumon weight estimate), applied in complementary degrees and
   combined with Poincaré duality;
3. the weight estimate proved by devissage to curves and the
   *Fourier–Deligne transform* on the affine line, with four sharply
   isolated deep leaves (real-sheaf purity, boundary monodromy, local
   Fourier theory, tame reduction).

*Route choices made explicit.* The blueprint does *not* use the Weil I
route (Lefschetz pencils, Kazhdan–Margulis, rationality of pencils): that
route needs hard Lefschetz, pencil geometry, and heavy monodromy theory,
while the Fourier route needs a much narrower six-operation fragment. It
also does not use Dwork's $`p`-adic proof of rationality: rationality falls
out of the $`\ell`-adic factorization for free, and the $`p`-adic apparatus
would be used nowhere else. *Perverse sheaves are omitted from the critical
path*: the one place where perverse language is customary (concentration of
the Fourier transform of a middle extension in one degree) is replaced by a
sheaf-level concentration lemma ({bpref "PUR-fourier-concentration"}[]);
perverse machinery survives only inside the internal decomposition of the
local Fourier deep leaf, which is initially a temporary axiom. Similarly,
*no spectral sequences* appear anywhere: every Leray-type argument is
consumed through a finite Frobenius-stable filtration with controlled
graded pieces ({bpref "WT-filtration-bound"}[]).

# Three abstraction layers

* *Layer I — graded Frobenius linear algebra* (chapters: Elementary
  foundations, Frobenius modules, Zeta functions, Final assembly). A
  purely algebraic theorem: finite-dimensional graded vector spaces with
  automorphisms, a trace identity, similitude pairings, an endpoint
  normalization and universal purity produce all conclusions. No schemes,
  no sheaves.
* *Layer II — abstract Weil cohomology package* (chapter: Abstract
  cohomology package). The bundled interface {bpref "COH-weil-package"}[]
  with exactly four substantive fields (AX1–AX4) plus a cardinality bound.
  The interface is *minimal*: no functoriality, no Künneth, no cycle
  classes, no cup products beyond one sign, no weak or hard Lefschetz —
  each exclusion is justified by the fact that no downstream node uses it.
* *Layer III — étale realization* (chapters: Trace formula, Duality,
  Étale cohomology, Six operations, Weights, Purity, Deep geometric
  inputs). $`\ell`-adic étale cohomology satisfies the interface. Each
  deep input is exposed as its own node; nothing is hidden inside the
  realization theorem {bpref "ET-realization"}[].

# Node identifiers, tags, and dependency discipline

Stable node prefixes: `W-` final statements; `Z-` zeta functions and formal
series; `LA-` linear algebra and field theory; `ML-` verified Mathlib
leaves; `TR-` trace formula; `DU-` duality; `WT-` weights; `COH-` abstract
package; `ET-` étale realization; `SH-` sheaf categories; `SIX-` individual
operations; `MON-` monodromy; `GEO-` geometric reductions and deep
realization inputs; `PUR-` the purity proof; `LFT-` local Fourier theory.

Tags: `mathlib` (the linked declaration was verified in the pinned Mathlib);
`existing-project` (formalized in this repository); `elementary-missing`
(elementary mathematics, no Lean counterpart yet); `infrastructure`
(substantial new formal infrastructure); `deep-input` (deep theorem);
`temporary-axiom` (planned interface axiom until eliminated); `blocked`
(waiting on an unformalized prerequisite).

Dependency discipline: a node's `uses` lists only what is needed to
*formulate* it (statement dependencies); the `uses` of its `:::proof` block
lists what the *proof* consumes (proof dependencies). The two are never
mixed, and the generated graph distinguishes the two edge kinds.

A node exists only when it has an independent mathematical statement,
corresponds to a distinct future Lean declaration, isolates a deep theorem,
or exposes a genuine dependency boundary. Conversely no node bundles
several theorems: the summary page's actionable/blocked classification is
only meaningful at that granularity.
