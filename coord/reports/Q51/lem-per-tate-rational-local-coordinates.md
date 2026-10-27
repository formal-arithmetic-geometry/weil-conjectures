# Stage-1 report: lem-per-tate-rational-local-coordinates

## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-tate-rational-local-coordinates.json: statement, split into seven steps; statement unchanged; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-tate-banach-substitution.json: new statement-only analytic lemma, unsplit; no Mathlib match after LeanFinder, Loogle, LeanSearch and source-grep searches, including a second phrasing.
- citations.json: eight step/node entries, with verbatim statement excerpts.
- report.md: this report. searches.jsonl is the search command's unmodified log.

## Attachments

None. I searched lean/WeilConjectures for the exact blueprint tag and for TateAlgebra, Tate algebra, restricted power series, and analytic evaluation/substitution terminology. The Tate references found there concerned Koszul complexes and residues, not rational points of convergent-series algebras. No project declaration giving all clauses was found. The existing off-unit affinoid comparison has a stated Lean theorem with sorry; it is used as a DAG input, not treated as a completed attachment.

## Sources wanted

WANTED: Brian Conrad, Several approaches to non-archimedean geometry, Exercise 1.1.3, Theorem 1.1.5(1), Exercise 1.2.8(3)-(4), PDF pp.3, 4, 7, for lem-per-tate-rational-local-coordinates and lem-per-tate-banach-substitution; archival path literature/conrad-several-approaches-non-archimedean-geometry.pdf. I read the Stanford PDF https://math.stanford.edu/~conrad/papers/aws.pdf online on 2026-10-24, but the archival copy is absent and I downloaded nothing.

WANTED: Bosch–Guntzer–Remmert, Non-Archimedean Analysis, basic Gauss-norm completeness and restricted-series regrouping, for the already existing lem-trf-restricted-series-gauss-completion. Its source already says the book is absent and gives no verified theorem number. No new claim about an unverified BGR page is made.

The item's proof is marked proof_origin.by = agent: Conrad gives the analytic context, but the monomial partition, prime chain, derivative-continuity argument and square-zero fraction calculation are written out here. The new lemma records its precise Conrad exercise and the missing local archive, rather than an invented Stacks tag. No SGA source is used.

## Problems found and changes

The imported item had a correct statement and no proof. I kept the statement and its statement dependencies. In particular the conclusion does not assume discrete valuation, algebraic closure, characteristic zero, or a point strictly inside the unit ball. I preserved the source and other maintainer fields.

The latest blueprint ancestor lem-per-artin-gabber-affine-curve has a duality Step 3, not a formal-algebraization argument. This is already explicitly recorded in the item's inherited blueprint.from.place. I read that current proof and the chapter and unit records. This delivery fills the assigned historical analytic prerequisite without claiming that the latest blueprint itself states it and without modifying the chapter or unit. The unit key nodes are thm-a1-curve-perverse-heart and thm-a1-fourier-t-exact; this item is not one, so there is no unit realization edit.

A tempting incorrect shortcut would be to use Mathlib's evaluation of arbitrary formal power series at norm-one inputs. I inspected Mathlib/RingTheory/MvPowerSeries/Evaluation.lean: HasEval requires each variable image to be topologically nilpotent, and the evaluation constructions require an ideal-linear topology. That does not apply to a point a_i with |a_i|=1 or to t_i+a_i in a Tate algebra. Mathlib/RingTheory/PowerSeries/Restricted.lean supplies a restricted-series predicate and subring operations but not the bounded substitution theorem. Algebra.Generators.cotangentSpaceBasis and the smooth-presentation results found by the other searches concern algebraic presentations, so do not identify this analytic cotangent space in one line. The new general substitution lemma is therefore an unsplit analytic input, not a Mathlib leaf.

The argument intended for that future node is the usual extension of polynomial substitution: each finite evaluated sum has norm bounded by the largest coefficient norm, so the cofinite coefficient-decay condition makes these sums Cauchy in B. Their limits respect addition and multiplication by approximation with polynomials and continuity of multiplication; the same estimate proves contractivity. A continuous map with the specified variable values agrees on polynomials, which are dense, hence agrees everywhere. This explanatory argument belongs here, not in the unsplit node's statement or proof fields.

## Not duplicates

lem-per-tate-banach-substitution vs lem-trf-restricted-series-gauss-completion: the existing node gives norm properties, completeness, polynomial density and regrouping; it does not assert homomorphisms into an arbitrary complete normed F-algebra or uniqueness of substitution.

lem-per-tate-banach-substitution vs lem-trf-affinoid-polynomial-closed-point-comparison: that node asserts Noetherian affinoid quotients and completed-local-ring comparisons for polynomial ideals. It does not construct substitution into a general Banach algebra. I reuse its Noetherianity for J=0 rather than creating a duplicate Tate-Noetherianity node.

lem-per-tate-banach-substitution vs lem-per-tate-maximal-residue-evaluation: that node describes residue fields at maximal ideals and the evaluation attached to those fields; it does not permit arbitrary complete algebra targets, which are needed for translations into another Tate algebra.

lem-per-tate-banach-substitution vs lem-trf-tate-weierstrass-norm-division: that node gives division and preparation for distinguished series; it gives no universal property for bounded tuples.

I searched the whole DAG for Tate algebra, restricted series, Banach, recentering, substitution, the Stanford source, and Exercise 1.2.8. I also ran tools/blueprint_refs.py search for Tate algebra, Banach algebra, Banach, restricted series, restricted power series, strictly convergent, substitution, recenter, Gauss norm, and cotangent space, and read the hits. No blueprint node states the new lemma or the item. Both same_as fields remain empty. The new name was absent before creation. There are no Stacks tags on the new node, hence no same-tag duplicate pairs.

## Review by Q51

I read delivery-errors B–E in full, including their mirrored sections, then reviewed the actual files rather than just the checks' output. For the item I read Conrad's theorem on the Tate ring and the recentering exercise online. For the sole new node I read his Exercise 1.2.8(3), which applies to Banach algebra targets, not just residue fields. Our norm-one-tuple version includes its contractive estimate explicitly and requires completeness, ultrametricity, compatible scalar norm, submultiplicativity, and a normalized unit. It is a general analytic construction with its own arbitrary target B; it does not restate regularity, the rational maximal ideal, or the cotangent formula of the item. It remains statement-only, with empty proof and proof_deps.

Step 1 cites the exact existing Gauss-completion statement for completeness and polynomial density, and the new substitution statement for maps with prescribed bounded variable images and uniqueness. The inequalities on the two substituted tuples use |a_i| <= 1. Composing the maps fixes each variable and is continuous, so uniqueness proves inverse maps; this also justifies calling them isometries. Evaluation in the target F is permitted by the same hypotheses. Neither cited statement is being used for an unstated derivative theorem.

Step 2 has a written coefficient partition, not a citation to a first-order/Taylor clause of the item. Its only cited node is localization-at-prime, whose statement explicitly gives the fraction equality relation and local maximal ideal. The fraction calculation proves that relation is respected by the residue map and checks that the numerator vanishes exactly when the residue does. Surjectivity of evaluation is proved by constants, so no unproved maximality theorem is used.

Step 3 uses only the Noetherianity clause of the affinoid-polynomial comparison, with polynomial ideal J=0 and precisely the same complete, nontrivially valued field F. The Noetherian definition states finite generation of every ideal, which the proof then transfers to localized ideals by contracting and multiplying a fraction by its denominator. The dimension node assumes a Noetherian local ring with an n-generated maximal ideal; these hypotheses have all been established before applying it with n=r. These two analytic nodes are declared generic off-unit tools in split_report.tool_uses; the dimension and regular-ring nodes are Mathlib leaves. No proof of a cited node is used in place of its statement.

Step 4 proves the dimension lower bound with actual prime ideals. The coefficient partition identifies every coordinate quotient, and the least nonzero homogeneous parts show that those quotients are domains (the only polynomial fact used is multiplication of leading monomials over a field). The written contraction argument checks that a strict prime chain stays strict after localization, since all its primes are contained in the evaluation kernel. This avoids silently inferring equality of dimension from the number of cotangent generators. The regular-ring definition says exactly that a Noetherian local ring whose maximal ideal has dim R generators is regular, which is now applicable.

Step 5 cites Gauss completeness/density only for passage from polynomial truncations to restricted series. Differentiation is bounded by one even in positive characteristic: the absolute value of a natural integer is at most one, and some of those integers may vanish. The derivative remains restricted by the explicit coefficient bound. This proves the linear coefficient identity by limits, and the degree-one Cauchy product formula is then a finite coefficient calculation.

Steps 6 and 7 cite no additional nodes: they spell out algebra in the explicitly defined square-zero ring F plus F^r. The inverse of j(u) is computed and the localization equality is checked after applying j and cancelling units. The image of m has zero scalar component, so products of two such images vanish. This proves the descent through m/m^2 and the precise numerator/denominator formula without assuming representative independence. Finally r_i differs from its residue by an element of m, which gives spanning over F; the coordinate vectors prove both inverse identities. No non-elementary input is hidden behind a word such as transport or clear denominators.

Small cases: at r=0 the rings and scalar map are F, the ideal and spaces are zero, and the proof explicitly covers this. For r=1 and a=0 the coefficient partition is division by x and the cotangent coordinate is the ordinary linear coefficient. Boundary points |a_i|=1 still give bounded translations and inverse translations. In characteristic p, d(x_i^p)=0 as required while d(x_i-a_i)=1, so there is no separability hypothesis hidden in the cotangent basis. For the new substitution lemma, an empty tuple gives the scalar map, all b_i=0 gives the constant coefficient, and b_1=1 is allowed; the last case explains why formal-series topological-nilpotence lemmas are insufficient.

All seven steps are shorter than 2000 characters. The only general analytic identification needed by them, bounded substitution, has been extracted as a node. I checked C1/C4 against each cited statement and wrote citations.json using verbatim portions of those statements. All other operations are explicit coefficient partitions, finite algebra or the given definitions. No statement dispute, added hypothesis, hollow definition, Lean edit, compiler run, or route change is present.

## Unfinished work

No part of this stage-1 split remains unfinished. The new analytic node is deliberately unsplit and queued for its own stage-1 work; this delivery does not claim a Lean proof of it.
