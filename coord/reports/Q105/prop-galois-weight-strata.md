# Worker report: prop-galois-weight-strata

## Files written

- `dag/nodes/sec-zeta-weil/prop-galois-weight-strata.json`: statement, split into four proof steps; unchanged mathematical statement; no whole-item Mathlib match.
- `dag/nodes/sec-zeta-weil/lem-weil-root-multiplicity-injective-map.json`: statement, Mathlib leaf `Polynomial.eq_rootMultiplicity_map`, `Mathlib/Algebra/Polynomial/Roots.lean:905–912`. One new node, one Mathlib leaf.
- `citations.json`: a verbatim statement quotation for all six citations in the item's proof.
- `searches.jsonl`: actual Mathlib searches recorded by msearch.py; no inherited searches existed.

## Attachments

None. The whole-tree Lean searches for the blueprint tag, Galois/weight terms, Weil numbers, and reciprocal-root terminology found no declaration stating the item. I read `WeilConjectures/ZetaLinearAlgebra/WeightStrata.lean`, including `Polynomial.roots_map_weightFactor` and its definition of `weightFactor`, and the predicates and declaration list in `Weights.lean`. Those results describe a normalized rational factor's complex ordinary-root multiset using a minimal-polynomial purity predicate. They do not state this item's Galois action on the specified reciprocal-root multisets in the fixed algebraic closure of Q. A derived argument and changes of representation would be required, so I make no ATTACH claim. No project declaration matching the new general coefficient-map lemma was found either. No compiler or Lake command was used.

## WANTED

None. Both blueprint snapshots and the pinned Mathlib source needed here were available locally.

## What was wrong and what changed

The imported proof compressed preservation of multiplicities into the assertion that a rational polynomial's root multiset is Galois-stable. I exposed its precise general tool as a Mathlib leaf, rather than introducing a new node restating Galois stability of a whole weight stratum. Step 1 computes reciprocal coefficients and their invariance; Step 2 applies the multiplicity-map theorem; Step 3 uses the existing intrinsic-weight Galois-stability statement; Step 4 performs the filter/count bookkeeping explicitly.

The item statement is identical to the repository and to the master source. The main-20261015 statement agrees too; there is no blueprint_update on this item. Its weight predicate, polynomial ring and multiplicity notions now appear in stmt_deps. The original setting dependencies were retained because the statement still introduces those objects, even though the polynomial argument needs no geometry. The ordinary/reciprocal-root definition's ell-adic setting does not by itself state the rational-polynomial multiplicity theorem, so it is not used as that theorem. The reciprocal formula is already explicit in the item, and Step 1 proves what is needed directly by coefficient reversal.

The uniqueness-of-weight and additional embedding-invariance assumptions are retained verbatim. The intrinsic all-embeddings weight definition already suffices for stability, so those stronger contextual assumptions need not be used. This is not a correction or weakening of the statement. The unit and chapter routes are unchanged: this is exactly the rationality part (i) of the unique step of sk-thm-intfactors. The item is not the unit's key statement, so no unit record was written.

## Searches and duplicates

Before creating the leaf, I searched the whole DAG for `rootMultiplicity_map`, `map_rootMultiplicity`, root multiplicities under injective maps, Galois/root multisets and multiplicities under automorphisms. I ran blueprint_refs searches for `Galois weight`, `Galois`, `multiplicity` and `root`, and its ancestor command. The ancestor is prop-galois-weight-strata itself. No other blueprint node states either this item or the general multiplicity-map equality. The other weight-stratum nodes state integrality or identification, not this result. `def-weil-root-multiplicity` defines multiplicity; it does not state its behavior under maps. The mention of multiplicity mapping found in `lem-pur-quasifinite-flat-weighted-trace` is not in that node's statement, which concerns a sheaf trace, so that node cannot supply the equality. No Stacks source tag is attached to the new leaf, so no same-tag duplicate pair arises.

The item's first semantic search returned Galois actions on distinct roots, complex conjugation and root-of-unity/Frobenius results; the differently phrased LeanSearch returned Galois root-set actions and Polynomial.roots, not Weil-weight filtered multisets. The source grep found no Weil-number predicate in Mathlib/NumberTheory; Loogle `Polynomial.roots, AlgEquiv` returned no hits. Thus no whole-item match is claimed. For the new lemma the semantic searches returned root-transport inequalities and root-set/multiset maps. Loogle `Polynomial.rootMultiplicity, Polynomial.map` found the exact equality, and msearch source grep located it at Roots.lean:905. I opened lines 895–925 and checked both the signature and proof. All four search records for the new node are actual logged queries, and the recorded verdict distinguishes the exact equality from the nearby weaker inequalities. No service was unavailable.

## Review by Q105

I read the master file `literature/blueprint/master/blueprint/sec-zeta-weil/sk-thm-intfactors/prop-galois-weight-strata.md`, its complete proof, the matching main-20261015 file, `dag/units/sk-thm-intfactors.json` and `dag/chapters/sec-zeta-weil.json`. The source fixes the same finite fields, coefficient closures, smooth proper family, normalized integral A and B, parity convention, reciprocal polynomials, integer weight interval and hypotheses as the unchanged statement. The unit's point (i) asks precisely for rational coefficients to preserve roots and intrinsic weight to preserve each stratum. This split supplies those arguments rather than substituting another unit route. No SGA source is used.

For Step 1 I opened `def-weil-polynomial-ring` and `def-weil-coefficientwise-ring-hom-map`. Their statements give, respectively, the finite coefficient expansion and the coefficientwise ring map fixing the variable. From c_0=1 and c_r nonzero I wrote out the reversed expansion, leading coefficient and constant coefficient. Integer coefficients embed in Q and then Qbar; an automorphism over Q fixes each coefficient. This is elementary coefficient bookkeeping, including the constant polynomial case, not an invocation of an uncited reciprocal-polynomial theorem.

For Step 2 I checked the new leaf against `Polynomial.eq_rootMultiplicity_map`, Roots.lean:905–912. Its hypotheses are commutative rings and an injective ring homomorphism; two fields and the automorphism gamma satisfy them. In particular it asserts equality, whereas the adjacent `le_rootMultiplicity_map` only asserts an inequality and has a nonzero mapped-polynomial hypothesis. The equality theorem explicitly handles P=0, so the new node does not accidentally omit or invent that case. I also opened `def-weil-root-multiplicity`, whose statement identifies multiplicity and says positive multiplicity is equivalent to being a root for a nonzero polynomial. The computed monic f is nonzero. Those two cited statements justify the full multiplicity claim; no uniqueness-of-factorization or splitting-field theorem is being silently used.

For Step 3 I opened `def-weil-numbers` and `lem-embedding-extension`. The former quantifies over every Q-embedding of Q(alpha) into C, and the latter's final sentence explicitly says the weight-i condition is stable under Gal(Qbar/Q). I use exactly that final assertion; I do not take arbitrary-extension or transcendence-basis data from its proof. The finite-field datum and fixed closures agree with the item. Applying this assertion also to gamma inverse gives equivalence rather than only forward membership. The displayed composite embedding explains why the all-embeddings formulation is the right one. The value zero is excluded by definition, and automorphisms fix zero. The citations quote the actual final sentence rather than an unrelated embedding-extension clause.

Step 4 only substitutes the two established equalities into the definition of a submultiset: count(x) is m_x(f) or zero according to W_i(x). For the image under a bijection, the sole preimage of y is gamma inverse(y), so there are exactly that many copies. This gives equality of multisets, not merely equality of root sets. No non-elementary lemma is hidden in this finite bookkeeping step.

For the new leaf I checked B1–B9 directly: its statement independently introduces both fields, the map, the polynomial and the root; it cites the existing field, polynomial, coefficient-map and multiplicity definitions; it has empty proof and proof_deps, single TeX backslashes, exact declaration/file/line evidence, and correct ancestry and unit. It is strictly smaller than the item, with no Weil number, geometry, or Galois-stratum conclusion. The source is an exact available Mathlib theorem, not a guessed Stacks tag. Searches covered the whole existing DAG and imported blueprint before creation.

Small cases checked: C=1 produces the empty multiset; an empty weight stratum remains empty; a repeated root such as P=(U-x)^3 retains multiplicity 3 under the coefficient map; a nonroot retains multiplicity zero; P=0 in the leaf has multiplicity zero by the explicit convention; f(0)=c_r excludes zero roots even when f has no roots to test. The argument covers both parities and i=0 or i=2d, and d=0 introduces no extra case. There is no separability, distinct-roots, chosen-complex-embedding, or ell-adic comparison assumption in the new lemma. Uniqueness of weight is not used to infer multiplicity preservation. No step exceeds 2000 characters (lengths 555, 528, 690, 563), and each non-elementary input is cited as a statement. I corrected the original compression and the incomplete statement-dependency list; no statement dispute remains.

## Unfinished work

None in this one-level split. The existing embedding-extension node remains a cited DAG dependency; proving it is not part of this item. The independent maintainer review remains the delivery acceptance gate.

## Validation repair

The first server dry run required an explicit `mathlib_match.line` field. The declaration and its source lines were already read and recorded in `how`; I added the required numeric `line: 905`. No mathematical statement, proof step, or citation changed.
