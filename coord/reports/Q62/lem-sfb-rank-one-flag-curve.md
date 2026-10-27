# Stage-1 delivery: lem-sfb-rank-one-flag-curve

Files written:

- `dag/nodes/sec-six-functors-basics/lem-sfb-rank-one-flag-curve.json`: unchanged statement, four proof steps, status split. Original statement dependencies and inherited search records retained; actual Q62 searches appended.
- `dag/nodes/sec-six-functors-basics/lem-sfb-proper-homogeneous-torus-fixed-bound.json`: one new statement-only lemma, status unsplit, no Mathlib match. This is Milne Corollary 20.12 for arbitrary proper homogeneous quotients and arbitrary torus subgroups.
- `citations.json`: one verbatim statement quotation for each citation of each proof step.
- `searches.jsonl`: actual msearch records. `milne.txt` is the local PDF extraction and `prepare.py` is the sandbox preparation script; neither is a project delivery file.

Attachments: none. Searches of `lean/WeilConjectures/` by the item tag and by Borel, semisimpleRank, flagVariety, torus fixed points and homogeneous fixed points found no declaration stating the item or the new lemma. The inherited item has no Lean declaration to attach.

WANTED: none. The Milne PDF and Stacks sources needed for this split are present.

What was wrong: the item was statement-only. Its statement agrees with the reductive case of Milne Theorem 20.16(a) implies (c) and is retained verbatim. Milne's printed deduction from the fixed-point bound omits the explicit exclusion of dimension zero; step 4 supplies that argument. No false source statement or route error was found. No unit record is changed: this supporting node is not the unit's key statement.

What remains: the new general fixed-point estimate is deliberately unsplit, as the one-level rule requires. The existing opposite-Borel node remains an existing dependency; only its assertion that there are two Borels is used here. There is no unfinished argument in the item's assembly proof.

## Source and route

I read Milne, *Algebraic Groups* (iAG2017), printed pp.410--413: Proposition 20.11, Corollary 20.12, Lemma 20.15, and Theorem 20.16. The item follows (a) implies (b) implies (c). The first implication is already stated, together with an extra intersection assertion, in `lem-sfb-rank-one-opposite-borel-intersection`; duplicating its two-Borel clause would violate the brief. Its two-Borel assertion is the implication proved before the flag-curve deduction in Milne. No use is made of its stronger scheme-intersection assertion or of the subsequent PGL2 classification. A source-only dependency traversal confirmed that this node and every other cited node have no dependency path to the item.

For the new lemma I read the full proof of Corollary 20.12 and its proof input Proposition 20.11. The corollary realizes G/H as a closed projective orbit for a representation and applies the torus fixed-point bound for projective linear actions. The argument is a genuine general lemma, not the rank-one item in other words: it assumes neither reductivity nor semisimple rank one, imposes properness on G/H, permits nonmaximal and trivial tori, and gives a dimension bound rather than dimension one. Its projective weight-space fixed points are stable after every algebra extension, so the statement uses scheme-theoretic fixed points. The new node contains only its statement, source, definition dependencies and search results, with no proof sketch hidden inside its statement.

The latest blueprint files read were `sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`, its proof, and its direct-images proof. The historical unit record and the current blueprint differ in layout; this delivery changes neither. This node serves the inherited auxiliary rank-one group argument on the alteration route. The ancestry tool reports `blueprint.from.node = None`, as in the live item; I preserve that and extend its precise inherited place and via chain for the new lemma. Whole-blueprint searches for rank one, torus fixed, homogeneous torus, and fixed point bound found no node stating the new estimate. Whole-DAG searches by fixed-point/dimension concepts and Milne 20.11/20.12 likewise found no duplicate; numerical coincidences in other sources were checked by statement, not treated as matches.

## Mathlib searches

The item and the new node were searched with msearch LeanFinder, LeanSearch, Loogle and grep. The new estimate received a second semantic phrasing. All these services answered. Every recorded query is copied from the command's actual log; no unavailable service is called a negative result. The first broad grep for tori included false positives such as `toRing...` and `Functorial`; a second grep with word boundaries returned zero algebraic-geometry hits.

I read `Mathlib/GroupTheory/GroupAction/Defs.lean:116` (fixedPoints is merely a set definition), `Mathlib/FieldTheory/Fixed.lean:265` and `:303` (rank/finrank over a fixed subfield for finite groups), and `Mathlib/LinearAlgebra/Projectivization/Cardinality.lean` (cardinality of all projective lines over finite fields). They have different objects and conclusions from the requested scheme-dimension bound. The item's hits similarly concern Lie-algebra Borel submodules, module ranks or measurable Borel spaces. No result specializes in one line to either statement.

## Not duplicates

lem-sfb-proper-homogeneous-torus-fixed-bound vs lem-sfb-general-borel-flag-variety: the existing lemma constructs the flag scheme and identifies its fixed points with Borels; it gives no dimension lower bound on their number.

lem-sfb-proper-homogeneous-torus-fixed-bound vs lem-sfb-general-flag-isolated-linear-action: the existing lemma supplies an isolated-fixed-point one-parameter action and a projective embedding for a Borel quotient; it gives no dimension-plus-one estimate for arbitrary torus subgroups on arbitrary proper homogeneous quotients.

lem-sfb-proper-homogeneous-torus-fixed-bound vs lem-sfb-projective-torus-fixed-weight-schemes: the existing statement describes fixed subschemes in weight coordinates and separates weights; it gives no lower bound on how many fixed points a closed invariant projective variety contains.

## Review by Q62

I checked B through E of delivery-errors against the files and sources, including the duplicate second copy of those sections. The new statement introduces every object and every hypothesis, cites the definitions it needs, has empty proof and proof_deps, and retains the blueprint origin and via chain. The item is an argument, not an application of a renamed conclusion: it identifies the homogeneous scheme, counts its fixed flags using existing work, bounds its dimension with a general geometric estimate, and rules out the remaining value zero. No step exceeds 2000 characters. No new statement is elementary, a duplicate, a clause of the item, or a Mathlib theorem.

Step 1 uses the full statements of general-borel-flag-variety (smooth connected projective scheme, transitivity and exact scheme stabilizer B), smooth-group-orbit-geometry (smooth locally closed orbit), and homogeneous-orbit-quotient-geometry (that reduced orbit is the represented G/B). I checked that reductivity gives the required smooth connected affine finite-type G, and that the flag scheme is separated finite type. The closed-point-residue-field-base statement identifies every closed residue field with F, and the lft-over-field-jacobson-space statement gives density in every closed subset. These identify the orbit with the whole flag scheme, including the empty-complement argument. I corrected an initially implicit use of smoothness implying reducedness by adding the existing smooth-geometrically-reduced node; the scheme equality is then explained by the radical ideal of a reduced locally closed subscheme. This avoids asserting equality of schemes solely from equality of rational points.

Step 2 uses exactly the first conclusion of rank-one-opposite-borel-intersection: its reductivity, maximal torus, radical, fppf quotient and dimension-one rank hypotheses coincide with those of the item. General-borel-flag-variety explicitly says that scheme-theoretically torus-fixed points are precisely the points associated to Borels containing T, and its bijection makes the two points distinct. I did not infer this from a definition node or from only a set-theoretic stabilizer.

Step 3 uses exactly the statement of the new fixed-point estimate, with H=B and S=T. The Borel is closed, the maximal torus is a torus over the algebraically closed field, and properness and the quotient identification were established in step 1. Its at-least-d+1 conclusion and the two-point upper bound give d<=1 by arithmetic. There is no hidden reductive-group classification in this step.

Step 4 uses finite-type-dim-zero-artinian for the finite discrete topology, not a definition of dimension or a theorem about only affine schemes. I checked its source Stacks Tag 00KH, algebra-lemma-Noetherian-dimension-0, whose proof gives the discrete spectrum. Connectedness and nonemptiness force a singleton. The cited closed-point-residue-field-base statement then ensures this singleton supports just one F-point: maps from Spec F factor through the residue field and the F-algebra map from that field is unique. This contradicts step 2. This is why the proof obtains equality rather than merely an upper bound.

I tested the statements and argument on SL2 and PGL2 in every characteristic, especially characteristic two, and on GL2 where the radical is a positive-dimensional central torus. The proof never replaces the full maximal torus of G by a one-dimensional one, so GL2 is handled correctly. A torus G is outside the item's rank-one hypothesis. For the new bound, G=H gives one point and d=0; a trivial S fixes the entire space, so the estimate allows infinitely many fixed points. No finite fixed-locus assumption, smoothness of H, or characteristic-zero restriction was added. All citation quotations were checked against the actual statements. No Lean was written or compiled, no agent was started, and writes were confined to the assigned sandbox.
