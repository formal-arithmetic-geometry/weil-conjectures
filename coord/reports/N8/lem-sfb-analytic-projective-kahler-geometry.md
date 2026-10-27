# N8 — lem-sfb-analytic-projective-kahler-geometry

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-analytic-projective-kahler-geometry.json`: item, statement unchanged, split into seven explicit proof steps.
- `dag/nodes/sec-six-functors-basics/lem-sfb-finite-dimensional-sphere-compactness.json`: statement, Mathlib leaf `isCompact_sphere`, `Mathlib/Topology/MetricSpace/ProperSpace.lean:47`, using the inferred instance `FiniteDimensional.proper_real`, `Mathlib/Analysis/Normed/Module/FiniteDimension.lean:562`.
- `dag/nodes/sec-six-functors-basics/lem-sfb-local-ddbar-potential-calculus.json`: statement only, unsplit; arbitrary-dimensional local complex Hessian, closedness, holomorphic pullback and vanishing on logarithmic changes of frame. No exact Mathlib match.
- `citations.json`: verbatim portions of every cited node statement for every proof step using it.

## Attachments

None. Searching `lean/WeilConjectures/` for the item's blueprint tag, Fubini–Study and projective Kähler geometry found no declaration asserting this item. Ring-theoretic Kähler differentials do not concern this statement.

## WANTED

WANTED: Jean-Pierre Demailly, *Complex Analytic and Differential Geometry*, I §3.C (3.13)–(3.19), V §15.A, VI §4 (4.1) and (4.4), for the item and `lem-sfb-local-ddbar-potential-calculus`. The expected local path `literature/demailly-complex-analytic-differential-geometry.pdf` does not exist. I read the author's PDF online at https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/agbook.pdf (version June 21, 2012), printed pp.23–25, 277, 279, 296–297. I did not write to literature or download a replacement. The proof is marked agent-written, with the exact online source and local absence recorded.

## Source and scope

The original statement is mathematically consistent and is retained verbatim, including its normalization and the zero-dimensional convention. I read `GOAL.md`, the chapter and unit records, and the latest blueprint's `sk-thm-sf-ctf-stability/_section.md` and `sk-thm-sf-ctf-stability-direct-images.proof.md`. This is a supporting analytic input below the existing GAGA/Kodaira chain of direct-images (3); it replaces no unit-level argument. The unit record happens to name the earlier `sec-six-functors` chapter, while this item is in `sec-six-functors-basics`; I retain both inherited fields. The ancestor command prints `None`, consistently with the item's existing `blueprint.from.node: null`; both new nodes retain that computed ancestor and extend its exact existing via chain.

The imported node had no proof, not a completed Lean proof. Demailly explains compactness by a sphere quotient and supplies homogeneous charts and the normalized section in V §15.A. VI §4 (4.4) gives the Fubini–Study potential; I supply the Hausdorff separation, countable basis, overlap calculation, full Hessian and positivity calculation. The proof does not cite Chern curvature or a theorem that projective space is already Kähler, which would merely repeat a clause of the item.

## Searches and not duplicates

All Mathlib searches in the node files were executed with the required `batch2/msearch.py`; their results are in the untouched `searches.jsonl`. I read all returned hits, then the actual declarations at `ProperSpace.lean:47–49`, `FiniteDimension.lean:553–564`, and `Harmonic/Constructions.lean:107–109`. The latter is a one-variable harmonicity assertion, not an arbitrary-dimensional differential-form or pullback theorem. Two semantic phrasings were run for the new analytic lemma and for compact spheres. Additional Cauchy–Schwarz searches were exploratory; the final proof expands a sum of squares and creates no Cauchy–Schwarz node. Existing inherited item searches were preserved.

Before creating the nodes I searched all `dag/nodes` statements for unit spheres, closed bounded compactness, complex Hessians, pluriharmonicity and Wirtinger calculus; searched all project source for the blueprint tag and the analytic notions; and ran `tools/blueprint_refs.py search` for Fubini, complex manifold, sphere, compact sphere, potential, Hessian, pluriharmonic, Dolbeault and finite-dimensional. No blueprint node states either new assertion. The broad `finite-dimensional` query lists generic linear algebra, not sphere compactness.

## Not duplicates

- lem-sfb-finite-dimensional-sphere-compactness vs lem-weil-l-adic-extension-proper: the existing node concerns properness of a finite extension of a particular nonarchimedean field; the new leaf asserts compact spheres in arbitrary finite-dimensional real normed spaces.
- lem-sfb-finite-dimensional-sphere-compactness vs lem-sfb-analytic-projective-kahler-geometry: compactness of a sphere is a strictly smaller general topological input; the proof still constructs the projective quotient and proves its compactness by pulling back open covers.
- lem-sfb-local-ddbar-potential-calculus vs lem-sfb-chart-exterior-derivative-square-zero: the existing Mathlib leaf gives only the square-zero identity for the real exterior derivative; the new statement also supplies the complex Hessian, reality, holomorphic pullback, and vanishing on logarithmic frame changes in arbitrary dimension.
- lem-sfb-local-ddbar-potential-calculus vs lem-sfb-complex-analytic-function-operations: the existing leaf gives operations on analytic functions, not differential forms or the transformation of second derivatives.
- lem-sfb-local-ddbar-potential-calculus vs lem-sfb-local-scalar-dolbeault: the latter concerns solving the local Dolbeault equation, not the complex Hessian or its transformation law.
- lem-sfb-local-ddbar-potential-calculus vs lem-sfb-analytic-projective-kahler-geometry: the new statement asserts neither projective topology, positivity, nor existence of a Kähler metric. It is a general coordinate-calculus tool used in an overlap argument carried out in the item.

There are no Stacks tags in these analytic statements and thus no same-tag pair. No SGA source is used.

## Review by N8

I checked delivery-errors B–E against the written files, reading the cited statements rather than their proof sketches. Both new statements introduce their own objects; finite dimensionality cites its definition, and all differential-form and complex-derivative conventions are inline in the analytic lemma. Each is statement only, with no deferred argument in its statement or proof dependencies. The original field node and the existing analytic-operations leaf were opened and their exact statements read.

For step 1 I used `lem-sfb-complex-analytic-function-operations`: its continuous-linear, inversion, multiplication, finite-tuple and continuity clauses justify continuity of the ratios where the chosen denominator is nonzero. I explicitly proved openness of the quotient using saturation, hence did not assume that every quotient restricts to a quotient map on an arbitrary subset. The coordinate inverse is the normalized representative. Pullbacks of rational balls are a countable basis because there are finitely many charts, and every point of an open set lies in a chart where a rational ball can be chosen inside that set.

Step 2 is an elementary separation argument: the scalar-invariant rank-one matrix has image exactly the original line, so two inequivalent vectors give distinct matrices. One distinct real component separates them by disjoint inverse images of intervals. There is no claim that quotient spaces are automatically Hausdorff, and no use of compactness to infer continuity of an inverse.

For step 3 I read the new sphere statement and Mathlib source. Its hypothesis is finite dimensionality over the reals, satisfied by the explicit real basis of complex coordinate space. The radius is 1. I wrote out the open-cover argument for the continuous surjection instead of citing an unrecorded image-compactness theorem. Normalization is legal since the representative is nonzero. This step is non-elementary only at sphere compactness.

For step 4 the existing analytic-operations node has exactly the closure under division by a nonzero function and finite tuples required for the transition maps. The source charts and sections are Demailly V §15.A, p.277. I checked the inverse transition and both maps' domains; the normalized section never hits the removed zero vector. The chart target is the whole complex coordinate space, so there is no boundary.

For step 5 I read Demailly I §3.C, especially (3.17) and (3.19), as well as V (15.8) and VI (4.4). The new calculus statement explicitly supplies each of reality, smoothness, closedness, linearity, holomorphic pullback and the log-modulus zero clause. The transition identity is proved inside the step: dividing the normalized vector by its lth coordinate divides its squared norm by that coordinate's squared modulus. This coordinate is nowhere zero on precisely the overlap. Hence subtracting its log squared modulus does not change D. I did not assume a global logarithm of a nonzero holomorphic function. Equality on overlaps glues the tensor pointwise; all the asserted tensor properties can be checked in charts.

For step 6 I checked the mixed Hessian entries with the stated Wirtinger order and the factor i/(2 pi). Evaluation on (v,Jv) contributes the factor 1/pi, with a positive sign. The displayed sum-of-squares identity follows by expanding diagonal and off-diagonal terms; I wrote the expansion explanation in the step. Strict positivity comes from the separate sum of |a_r| squared, not from a strict form of Cauchy–Schwarz. Thus the argument also covers vectors parallel to w, w=0, and complex dimension 1. This is an elementary coordinate calculation using the explicit formula in the new calculus statement; it does not conceal an additional geometric lemma.

For step 7 I checked that g is the underlying real, J-invariant metric of the Hermitian form h=g-i omega (linear in its first entry); the formula gives both symmetry and positivity. This explains the conventional identification of a real Hermitian metric in the item. Closedness was already established, giving the Kähler condition of Demailly (4.1). In dimension zero there is one projective point, a zero-dimensional tangent space, zero differential form and a unique metric. The positivity quantifier has no nonzero vector, so no exceptional extra assumption has been introduced.

For the new calculus node, the source supplies the coordinate operators and their naturality. Its remaining proof to be split later uses equality of mixed real derivatives, conjugation of the Hessian, and the chain rule. In particular, for nowhere-zero holomorphic h, partial log |h| squared equals (partial h)/h, which has holomorphic coefficients; its bar derivative vanishes. Combining this with anticommutation gives partial bar-partial log |h| squared = 0, without choosing a global branch. This explanation is retained here, not smuggled into the statement-only node.

I tested the new sphere assertion also on negative radii (empty), zero radius (singleton), and the zero vector space (empty or singleton). The calculus assertion covers empty domains and dimension zero; it imposes no positivity claim and allows constant functions. No item step exceeds 2000 characters. The named non-elementary facts are cited, every citation has a verbatim quote, proof dependencies are exactly their union, and no dependency points upwards to the projective-geometry item. The report, search log and citations are retained for independent review.

## Unfinished work

The two new nodes are deliberately not split recursively: sphere compactness is a Mathlib leaf and the general local complex-Hessian lemma is queued as an unsplit statement. There is no unfinished step in the item's one-level split. Delivery validation is recorded by the required tool invocation.
