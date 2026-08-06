import Verso
import VersoManual
import VersoBlueprint
import WeilConjecturesBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Adversarial audit" =>

This chapter records an adversarial mathematical audit of the entire
dependency graph: every path from a Mathlib or elementary leaf to the
root theorem was re-examined, the functional-equation sign and all
normalizations were recomputed independently, the integrality and
independence-of-$`\ell` chain was checked line by line, and the
"perversity-free" claim of the Fourier route was stress-tested. The
audit found no mathematically incorrect node, one prose circularity,
and five places where the graph concealed genuine dependencies; all are
now corrected in the chapters, and the corrections are catalogued here.
This chapter is documentation only — it adds no nodes to the graph.

# Conventions table

Fixed once, consistent across all 156 nodes (re-verified in this audit):

* $`q = p^r`, $`k = \Fq`; $`\ell \neq p`; coefficients $`\Ql`,
  eigenvalue analysis after flat extension to $`\Qlbar`; abstract layers
  over algebraically closed $`K \supseteq \QQ`,
  $`\#K \leq 2^{\aleph_0}`.
* Frobenius on cohomology: *geometric* ($`F = \varphi^{-1}`), realized
  by the $`q`-power correspondence; fixed points of $`F^n` are the
  $`\Fqn{n}`-points; arithmetic-Frobenius eigenvalues are the
  inverses. Checked consistent in: {bpref "TR-interface-proper"}[],
  {bpref "TR-frobenius-fixed-points"}[],
  {bpref "ET-frobenius-dictionary"}[], {bpref "DU-tate-twist-action"}[].
* Zeta variable $`t`: formal (`PowerSeries ℚ`); no analytic
  convergence anywhere on the critical path.
* Tate twist: $`F` acts on $`\Ql(1)` by $`q^{-1}`, on $`\Ql(-d)` by
  $`q^{d}`; weight of $`\Ql(m)` is $`-2m`; duality multiplier is
  $`q^{+d}`; dual eigenvalue $`q^d/\alpha`. Pinned executably by
  {bpref "Z-normalization-tests"}[] and
  {bpref "ET-curve-computations"}[]; an arithmetic-Frobenius
  convention would flip the tests to reciprocal eigenvalues and is
  thereby excluded.
* Weights: squared normalization
  $`\|\iota\alpha\|^2 = q_x^{w}` with the *local* $`q_x = q^{\deg x}`;
  quantification over all ring homomorphisms
  $`\iota \colon K \to \CC`; base-extension invariance is now the
  explicit node {bpref "WT-base-extension"}[] (audit addition).
* $`H_c` versus $`H`: the final assembly sees only the package
  spaces; compact supports appear in {bpref "TR-interface-cc"}[] and
  throughout the purity branch; the identification for proper $`X` is
  always the explicit node {bpref "SIX-proper-comparison"}[], never
  implicit.

# Critical-path audit and classifications

Classification of the major nodes (every proof re-read against its
listed edges; classes: *justified* = completely justified by listed
dependencies; *missing-deps* = correct but previously missing explicit
intermediate dependencies — now fixed; *convention* =
convention-dependent, normalization re-verified).

* {bpref "W-log-zeta"}[], {bpref "W-factorization"}[],
  {bpref "LA-det-trace"}[], {bpref "LA-det-trace-graded"}[]:
  *justified*. The det–trace induction needs only one eigenvector,
  multiplicativity, additivity, and the exp/log package — all present
  as edges.
* {bpref "W-rationality"}[]: *justified*; audited line by line (see
  below).
* {bpref "W-no-cancellation"}[], {bpref "W-factor-identification"}[],
  {bpref "W-algebraicity"}[], {bpref "W-integral-coefficients"}[],
  {bpref "W-riemann-hypothesis"}[], {bpref "W-ell-independence"}[]:
  *justified* after the audit; {bpref "W-rational-coefficients"}[] was
  *missing-deps* (the weight-partition of the root multiset of $`A`
  needs {bpref "W-no-cancellation"}[] for disjointness and
  {bpref "LA-charpoly-rev-props"}[](iv) for the splitting — both edges
  added).
* {bpref "W-functional-equation"}[]: was *missing-deps* — the
  root-multiset predicate {bpref "Z-fe-predicate"}[] speaks about
  complex roots of *integer* polynomials, so its derivation needs
  {bpref "W-integral-coefficients"}[] (edge added); the proof now runs
  through the $`\ZZ[T, T^{-1}]`-descended Laurent identity, avoiding
  any multiset transfer between $`K` and $`\CC`.
* {bpref "DU-sign-analysis"}[] / {bpref "DU-graded-fe"}[]: the audit
  found a *prose circularity* (the sign formula was "read off" from
  the graded FE, whose proof cited the sign analysis). Fixed:
  {bpref "DU-sign-analysis"}[] proves $`\delta^2 = 1` and the
  determinant-product formula and *defines* $`\varepsilon`;
  {bpref "DU-graded-fe"}[] then proves the identity by direct
  substitution. The sign was recomputed independently (see below):
  the published formula $`\varepsilon = (-1)^\chi \delta^{(-1)^d}` is
  confirmed. Classification now *justified*; previously
  *convention/circular in exposition* (the mathematics was right, the
  edge direction was not).
* {bpref "TR-interface-proper"}[], {bpref "TR-interface-cc"}[],
  {bpref "DU-interface"}[], {bpref "DU-endpoint"}[],
  {bpref "COH-purity-input"}[]: temporary axioms; their realization
  subgraphs are complete (table below), so each is *unverifiable
  without an additional theorem* by design — with the additional
  theorem present in the graph as its elimination subgraph.
* {bpref "PUR-duality-squeeze"}[], {bpref "PUR-upper-bound"}[],
  {bpref "PUR-weight-estimate"}[], the six devissages: *justified*;
  {bpref "PUR-devissage-target"}[] was *missing-deps* (localization
  triangle edge added for the filtration gluing).
  {bpref "PUR-upper-bound"}[] is by design a specialization of
  {bpref "PUR-weight-estimate"}[] — not *equivalent in difficulty* to
  its consumer, because the general-sheaf relative statement is the
  forced induction vehicle (non-constant lisse direct images on
  strata), as its node explains.
* {bpref "PUR-projective-curve"}[]: was *missing-deps twice* — (a)
  the reduction to "$`\infty` in the lisse locus" was entirely
  absent (now {bpref "PUR-move-infinity"}[], with the base-extension
  lemma {bpref "WT-base-extension"}[] it silently needs); (b) step
  (v) misstated the direction of comparison: $`H^1(\mathbb{P}^1,
  j_*L)` is a *quotient* of $`H^1_c(\mathbb{A}^1, j_* L)` (fine for
  upper bounds), not a subobject. Both fixed.
* {bpref "PUR-affine-line"}[]: was *missing-deps* — see the Fourier
  section below. Now *justified* relative to the (smaller) axioms.
* {bpref "MON-boundary-m1"}[]: elimination script was
  *missing-deps* — the positivity step is invalid for a general pure
  sheaf; the real envelope {bpref "PUR-real-envelope"}[] must be
  applied first (edge added, text corrected).
* {bpref "MON-r1j-m2"}[]: *justified* (M1 for the dual + local
  duality + twist arithmetic; not an independent axiom).
* {bpref "PUR-real-purity"}[], {bpref "PUR-rank-one"}[],
  {bpref "MON-jordan-purity"}[], {bpref "LFT-stationary-phase"}[],
  {bpref "GEO-tame-reduction"}[]: deep leaves, statements re-read for
  scope-minimality; LFT was *rescoped* (below).
* Convention-sensitive nodes ({bpref "DU-tate-twist-action"}[],
  {bpref "ET-frobenius-dictionary"}[], {bpref "W-endpoints"}[]):
  *convention*, re-verified against the executable tests; no
  inconsistency found.

# The Fourier route: what "perversity-free" honestly means

The customary perverse-sheaf statement behind the Fourier argument has
*two* halves: (degree) the transform of a shifted middle extension is
concentrated in one degree; (shape) it is again a (shifted) middle
extension of an irreducible lisse sheaf. The previous graph proved
(degree) at sheaf level ({bpref "PUR-fourier-concentration"}[] — this
part genuinely needs no perverse formalism) but had quietly folded
(shape) into the statement of the temporary axiom
{bpref "LFT-stationary-phase"}[]. That was concealment by
terminology: an auditor reading only the node titles would believe
perversity had been eliminated, when in fact half of the perverse
package had been axiomatized.

The correction: (shape) is now the explicit node
{bpref "PUR-ft-middle-extension"}[], with a perversity-free proof from
Fourier inversion and Artin–Schreier orthogonality (punctual sheaves
and Artin–Schreier twists exchange under the transform, so a punctual
sub/quotient of the transform would produce a forbidden constituent of
the admissible input); {bpref "LFT-stationary-phase"}[] shrank to its
genuinely local content (local transforms on henselian traits, the
stationary-phase sequence at $`0'`, the unipotent block shape). The
curve $`t`-structure fragment survives only *inside* that smaller
leaf. Verdict: the critical path is perversity-free in statements and
in all proofs except the interior of one temporary axiom, where the
lecture notes themselves use the perverse language; intermediate
extension as an *operation* is never needed — only $`j_*` of lisse
sheaves on curves with its inertia stalk description
({bpref "SIX-j-star-curves"}[]).

# Line-by-line audit: integrality and independence of ℓ

Starting point: $`Z \in 1 + t\ZZ[\![t]\!]` — from the Euler product
over closed points ({bpref "Z-euler-product"}[], formalized), each
factor in $`1 + t\mathbb{N}[\![t]\!]`, locally finite product
({bpref "Z-integrality"}[]).

1. $`Z_K = O/E` with $`O, E \in K[t]`, constant terms $`1`
   ({bpref "W-factorization"}[] from AX1 + det–trace). *Enters:*
   trace formula, finite-dimensionality.
2. Coefficients of $`Z` satisfy a linear recurrence over $`K` beyond
   $`\deg O` (coefficient of $`t^n` in $`E \cdot Z = O`; uses
   $`E(0) = 1 \neq 0`). *Hankel enters:* finite Hankel rank over
   $`K` ({bpref "LA-linear-recurrence-hankel"}[], 2 ⇒ 4).
3. Hankel entries are rational; a nonzero minor is a nonzero element
   of $`\QQ`; *rank descent enters* ({bpref "LA-rank-descent"}[]):
   finite rank over $`\QQ`, hence $`Z \in \QQ(t)` (4 ⇒ 1).
4. *Fatou enters* ({bpref "LA-fatou"}[]): from
   $`Z \in \ZZ[\![t]\!] \cap \QQ(t)`, a presentation $`A_1/B_1` with
   $`A_1, B_1 \in \ZZ[t]`, $`B_1(0) = 1`, $`A_1(0) = 1` — via the
   shift lattice generated by *all* integral shifts and
   Cayley–Hamilton over $`\ZZ`.
5. *Gauss enters* ({bpref "LA-gauss-normalized"}[]): dividing by
   the normalized gcd gives coprime $`A, B \in \ZZ[t]` with constant
   terms $`1`; uniqueness by
   {bpref "LA-reduced-fraction-unique"}[]
   ({bpref "W-rationality-reduced"}[]).
6. *Purity and coprimality enter* ({bpref "W-no-cancellation"}[]):
   at a single $`\iota_0` (existence:
   {bpref "LA-embedding-extension"}[]), eigenvalues in distinct
   degrees have distinct squared norms $`q^i \neq q^j`
   ({bpref "WT-separation"}[]), so $`O` and $`E` share no root:
   coprime in $`K[t]`.
7. Coprimality of $`A, B` persists in $`K[t]` (Bézout); uniqueness of
   reduced normalized fractions identifies $`O = A`, $`E = B` in
   $`K[t]` ({bpref "W-factor-identification"}[]). *This is the exact
   point where the abstract determinant data becomes arithmetic.*
8. *Algebraicity is established here and not before*
   ({bpref "W-algebraicity"}[]): every eigenvalue is a reciprocal
   root of $`A` or $`B \in \ZZ[t]`; since $`A(0) = 1`, the reversal
   $`t^{\deg A} A(1/t)` is *monic* with integer coefficients, so all
   reciprocal roots are *algebraic integers*.
9. Every $`\sigma \in \operatorname{Aut}(K)` fixes $`\QQ`, permutes
   the root multiset of $`A` (splitting:
   {bpref "LA-charpoly-rev-props"}[](iv)) and preserves weight
   classes ({bpref "WT-aut-stability"}[] — this consumes the
   *universal* quantifier of AX4); disjointness of the weight classes
   (step 6) makes the weight-$`i` sub-multiset $`\sigma`-stable, so
   the coefficients of $`P_i` are fixed by all automorphisms, hence
   rational ({bpref "LA-aut-fixed-field"}[];
   {bpref "W-rational-coefficients"}[]).
10. *Gauss enters again* ({bpref "W-integral-coefficients"}[]):
    $`A = \prod_{\text{odd}} P_i` with normalized rational factors of
    a primitive integer polynomial forces $`P_i \in \ZZ[t]`.
11. *RH enters* ({bpref "W-riemann-hypothesis"}[]): each complex
    root $`z` of $`P_i` manufactures an embedding
    $`\QQ(\alpha) \to \CC`, extended to $`K` by
    {bpref "LA-embedding-extension"}[] (this consumes
    $`\#K \leq 2^{\aleph_0}`), and AX4 gives
    $`\|z\| = q^{-i/2}`.
12. *Independence of $`\ell`* ({bpref "W-ell-independence"}[]):
    $`A, B` are determined by $`Z` alone (step 5 uniqueness); by step
    11 the complex root multiset of $`A` is partitioned by modulus
    ($`q^{-i/2}` pairwise distinct since $`q \geq 2`), and $`P_i` is
    the unique normalized divisor of $`A` (odd $`i`) resp. $`B`
    (even $`i`) with all roots of modulus $`q^{-i/2}` — a
    characterization in terms of $`(Z, q, i)` only. The exponent
    $`\chi` and sign $`\varepsilon` are determined by $`Z` via
    {bpref "W-fe-uniqueness"}[]. Hence the exact independence
    statement: *any* realization of the package (any $`\ell \neq p`)
    produces the same $`(P_i)_i`, the same Betti numbers, the same
    $`\chi`, the same $`\varepsilon`.

Verdict on this branch: every step justified by graph edges; no use
of coprimality is asked to carry more than it can (in particular,
coprimality alone is *not* claimed to give integrality — steps 8–10
do that through algebraicity, Aut-descent, and Gauss).

# Independent recomputation of the functional equation

From the pairing data alone ($`\varphi_i` perfect,
$`\varphi_i(F_i x, F_{2d-i} y) = q^d\varphi_i(x, y)`, middle pairing
$`(-1)^d`-symmetric), without quoting the blueprint's conclusion:
transport gives $`F_{2d-i} = q^d (F_i^{-1})^\vee` under
$`H^{2d-i} \cong (H^i)^\vee`; hence
$`P_{2d-i}(T) = \det(1 - Tq^d F_i^{-1})`, and the endomorphism
identity $`1 - su^{-1} = (-su^{-1})(1 - s^{-1}u)` with $`s = q^dT`
yields $`P_i(1/(q^dT)) = (-q^dT)^{-b_i} D_i P_{2d-i}(T)`.
Substituting into
$`Z_F = \prod P_i^{(-1)^{i+1}}` and re-indexing $`i \mapsto 2d - i`:
$$`Z_F(1/(q^dT)) = (-1)^{\chi} q^{d\chi} T^{\chi} \Bigl(\prod_i D_i^{(-1)^i}\Bigr)^{-1} Z_F(T).`
With $`D_i D_{2d-i} = q^{d b_i}` and $`D_d^2 = q^{d b_d}` (taking
determinants in the transport), and $`d b_d` even (alternating
perfect middle form for odd $`d` forces even $`b_d`),
$`\prod D_i^{(-1)^i} = \delta^{(-1)^d} q^{d\chi/2}` with
$`\delta = D_d q^{-d b_d/2}`, $`\delta^2 = 1`; so
$$`Z_F(1/(q^dT)) = (-1)^{\chi}\, \delta^{(-1)^d}\, q^{d\chi/2}\, T^{\chi}\, Z_F(T),`
i.e. $`\varepsilon = (-1)^{\chi}\delta^{(-1)^d}` — *identical* to
{bpref "DU-graded-fe"}[]/{bpref "DU-sign-analysis"}[]. Test
($`\mathbb{P}^1`): $`\chi = 2`, $`\delta = 1`,
$`\varepsilon = +1`, and directly
$`Z(1/(qT)) = qT^2 Z(T)` ✓. Test ($`\Spec k`): $`d = 0`,
$`\chi = 1`, middle degree $`0`, $`D_0 = 1`, $`\delta = 1`,
$`\varepsilon = -1`, and directly
$`Z = (1-T)^{-1}`: $`Z(1/T) = (1 - 1/T)^{-1} = -T(1-T)^{-1} =
-T \cdot Z(T)` ✓ (exponent $`\chi = 1`, sign $`-1`). All powers of
$`q`, $`t`, and all signs confirmed; the sign is explicitly
$`(-1)^\chi \delta^{(-1)^d}`, computable from $`\det F_d`, and the
final combined theorem records the root-multiset form (signless) plus
this explicit classical form.

# Detected gaps and corrections (summary)

1. *Fourier shape half concealed in LFT* → new node
   {bpref "PUR-ft-middle-extension"}[]; LFT rescoped; PUR-affine-line
   rewired. (Concealed because the axiom's statement quietly included
   a provable global clause.)
2. *Unramified-at-∞ reduction absent* → new node
   {bpref "PUR-move-infinity"}[] (+ direction fix in
   {bpref "PUR-projective-curve"}[](v): quotient, not subobject).
   (Concealed because the affine-line estimate's hypothesis looked
   like a harmless normalization; it is a genuine reduction step that
   changes $`q`.)
3. *Base-extension invariance implicit* → new node
   {bpref "WT-base-extension"}[], consumed by the reduction above,
   the radicial devissage, and TAME. (Concealed inside "harmless
   finite extension" phrases.)
4. *Positivity without reality in the M1 capsule* →
   {bpref "MON-boundary-m1"}[] elimination now applies
   {bpref "PUR-real-envelope"}[] first. (Concealed by transferring
   the real-sheaf intuition to a non-real sheaf.)
5. *Sign-analysis/graded-FE prose circularity* → sign is now defined
   in {bpref "DU-sign-analysis"}[] and proved to be the FE sign in
   {bpref "DU-graded-fe"}[].
6. *Missing descent edges* →
   {bpref "W-rational-coefficients"}[] (+ no-cancellation, splitting),
   {bpref "W-functional-equation"}[] (+ integral coefficients),
   {bpref "PUR-devissage-target"}[] (+ localization triangle); and the
   double-listed statement/proof edge on
   {bpref "PUR-fourier-concentration"}[] resolved to a proof edge.

# Temporary axioms and their elimination subgraphs

* *AX1* {bpref "TR-interface-proper"}[] / {bpref "TR-interface-cc"}[]
  — eliminated by: {bpref "TR-l-function"}[] ⇐
  {bpref "TR-lefschetz-verdier"}[] +
  {bpref "TR-frobenius-local-terms"}[] +
  {bpref "TR-frobenius-fixed-points"}[] +
  {bpref "TR-closed-points-conversion"}[] +
  {bpref "TR-supertrace"}[] + {bpref "ET-adic-formalism"}[] +
  {bpref "SIX-proper-comparison"}[] (proper case) +
  {bpref "GEO-finiteness"}[].
* *AX2/AX3* {bpref "DU-interface"}[] / {bpref "DU-endpoint"}[] —
  eliminated by: {bpref "DU-poincare-duality"}[] ⇐
  {bpref "DU-cup-pairing"}[] ⇐ {bpref "DU-trace-map"}[] ⇐
  {bpref "GEO-duality-realization"}[]; plus
  {bpref "DU-tate-twist-action"}[], {bpref "ET-h0-computation"}[].
* *AX4* {bpref "COH-purity-input"}[] — eliminated by:
  {bpref "PUR-smooth-proper"}[] ⇐ {bpref "PUR-duality-squeeze"}[] +
  {bpref "PUR-upper-bound"}[] ⇐ {bpref "PUR-weight-estimate"}[] ⇐
  six devissages + {bpref "PUR-relative-curve"}[] ⇐ curve theorems ⇐
  {bpref "PUR-affine-line"}[] ⇐ Fourier nodes + the residual deep
  leaves {bpref "PUR-real-purity"}[] (with
  {bpref "PUR-rank-one"}[]), {bpref "MON-jordan-purity"}[],
  {bpref "LFT-stationary-phase"}[], {bpref "GEO-tame-reduction"}[]
  (eliminable by route (b)), over the six-operation fragment whose
  own debts are {bpref "GEO-proper-base-change"}[] and
  {bpref "GEO-finiteness"}[]. {bpref "MON-boundary-m1"}[] and
  {bpref "MON-r1j-m2"}[] have fully scripted eliminations and are
  scheduled to be proved, not axiomatized.

# Final verdicts

* *Rationality*: architecture *complete*. Modulo AX1 (cc form),
  every edge from Mathlib/elementary leaves to
  {bpref "W-rationality"}[] is present and individually elementary.
* *Functional equation*: architecture *complete*; sign and all
  normalizations independently recomputed and confirmed; no
  unexplained $`\pm` remains (the sign is
  $`(-1)^\chi \delta^{(-1)^d}` with $`\delta = \det F_d \cdot
  q^{-db_d/2} \in \{\pm 1\}`). Modulo AX2/AX3.
* *Riemann hypothesis*: architecture *complete modulo the audited
  deep leaves*; after the audit, the residual unproved content is
  exactly: PUR (with rank-one CFT inside), M3, the rescoped LFT,
  TAME (eliminable), and the two SGA-scale realization debts —
  each with its consumers and elimination plan explicit. No hidden
  perverse formalism remains on the critical path.
* *Integrality* (of the $`P_i` and of the zeta numerator/denominator):
  *complete*; the twelve-step chain above is fully edge-covered;
  algebraic integrality of reciprocal roots comes from monic
  reversals of normalized integer polynomials, established at step 8
  and nowhere assumed earlier.
* *Independence of $`\ell`*: *complete* as a uniqueness statement
  ({bpref "W-ell-independence"}[]); it requires the full RH pipeline
  for each individual $`\ell` and nothing comparing different
  $`\ell` — the graph reflects this exactly.
