# Worker report — Q09

Item: lem-sfb-trivial-ladic-derived-exterior. Stage 1 only; direct delivery.

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-trivial-ladic-derived-exterior.json: item, split into six steps; statement unchanged, no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-derived-bar-comparison.json: statement-only analytic comparison obligation, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-rational-polynomial-bar-contraction.json: statement-only universal rational algebraic contraction, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-internal-bar-ordered-cup.json: statement-only internal derived cup/bar normalization, unsplit; no Mathlib match.
- citations.json: a verbatim statement quotation for every step/node citation.

Searches are the genuine msearch.py calls in searches.jsonl. Every new node has LeanFinder twice with different phrasing, Loogle, grep, and LeanSearch. Results were read; no search service was treated as a negative result when unavailable. Source files for the plausible discrete bar/Ext, continuous topological cohomology, and condensed free/solid hits were read. None states these ordinary internal-module results. No Mathlib leaves were manufactured from the discrete representation API.

## Attachments

None. Searches of lean/WeilConjectures by the item's blueprint tag and by condensed invariants/cohomology, polynomial cochains and bar cup terminology found no project declaration giving the item. The exterior-power declarations concern algebraic representations and do not identify this derived group-invariants map. No compiler or Lake command was run.

## Literature wanted

WANTED: an exact reference for polynomial evaluation into the DERIVED internal bar totalization with ALL-continuous norm-topological algebraic-closure coefficients, for lem-sfb-polynomial-derived-bar-comparison. No completeness or solidity theorem is being silently applied to the noncomplete field.

WANTED: an explicit rational symmetric-coalgebra cobar/Koszul contraction with the ordered polynomial inclusion used here, for lem-sfb-rational-polynomial-bar-contraction. The mathematical reduction is to the unnormalized additive polynomial bar, not to the discrete group bar. The new lemma is an agent-formulated obligation, not attributed to an unrelated Stacks Koszul tag.

WANTED: an internal condensed bar/Alexander–Whitney comparison with the unital derived cup and the specified connecting-character normalization, for lem-sfb-internal-bar-ordered-cup. A discrete-group connecting-cocycle formula does not by itself prove the internal-module comparison.

The source fields identify the exact existing blueprint paragraph whose analytic base case these inputs serve. They explicitly mark the inputs as agent-formulated and their references wanted. The blueprint is not claimed to prove them. I also consulted the primary research text [Condensed Group Cohomology, arXiv:2512.03648](https://arxiv.org/html/2512.03648v1) for comparison scope, especially Theorem 2.5.8 and Remark 2.5.9; it does not supply the requested noncomplete coefficient calculation. No outside document was downloaded into the repository or sandbox. The split's proof_origin is agent.

## Corrections and scope

The original item had no proof. Its key issue is that an ordinary continuous-function cochain calculation alone does not establish ordinary internal condensed derived invariants. I have not changed its coefficient topology, statement, specified map, chapter, unit, source, created metadata, or blueprint ancestry. In particular I did not substitute the completion or the filtered union of finite-subextension sheaves. There is no established statement dispute or counterexample here.

The reduction uses two substantial independent mathematical inputs: an analytic comparison with the much larger polynomial bar complex, and a characteristic-zero algebraic contraction of that complex valid over every rational algebra. The third input fixes the generic derived cup arrow. None is a coordinate-cup derived-exterior theorem for the given field and lattice, and the item is not just an application of a renamed version of itself. The proof explicitly extends the contraction internally using finite rational matrices, composes the two derived isomorphisms, and identifies every summand of the specified arrow.

The chapter and unit records and the current main-20261015 paragraph (3) were read. This is a descendant analytic base case under open direct image, not the key node of the unit. The existing unit record still has older six-functor chapter metadata; it was not edited. The inherited blueprint ancestor command returns None and the recorded ancestry is preserved; the new nodes use that same returned ancestor and prepend this item to the via list. No SGA source is used. No off-unit proof theorem is substituted for the unit route; the polynomial-ring definition is only a statement dependency.

## What remains

The stage-1 split is complete; the three new nodes remain explicit statement-only obligations for later workers. In particular the all-continuous analytic comparison has not been proved or smuggled in as an elementary step. No claim is made that this delivery finishes the target in Lean or establishes that analytic lemma. There is no Lean writing and no local use of the prohibited DAG/preflight scripts.

## Not duplicates

lem-sfb-polynomial-derived-bar-comparison vs lem-sfb-condensed-derived-invariant-bar: the existing node identifies invariants with a DERIVED bar and explicitly disclaims underived continuous-cochain acyclicity; the new node asserts that a specified polynomial-evaluation map to that derived totalization is an isomorphism, without asserting column acyclicity.

lem-sfb-polynomial-derived-bar-comparison vs lem-sfb-condensed-product-bar-comparison: the existing node compares diagonal and iterated derived bars for product groups; it does not compare polynomial functions with a derived bar or treat this coefficient topology analytically.

lem-sfb-polynomial-derived-bar-comparison vs lem-sfb-dense-lattice-derived-invariants-comparison: the existing theorem compares profinite and discrete lattice invariants and already depends on this item, so using it would be circular; the new polynomial comparison has no dependency on that theorem, this item, or any exterior assertion.

lem-sfb-rational-polynomial-bar-contraction vs lem-sfb-discrete-lattice-cup-exterior: polynomial functions and addition substitutions over an arbitrary rational algebra are different from all functions on a discrete integer lattice; the new contraction is an algebraic homotopy, not a group-derived-invariants assertion.

lem-sfb-rational-polynomial-bar-contraction vs lem-sfb-integral-lattice-cubical-contraction: the existing lemma concerns integral chains on lattice cells with translation-difference boundary; the new one concerns rational polynomial cochains with addition-substitution boundary. Neither differential or basis is a specialization of the other.

lem-sfb-rational-polynomial-bar-contraction vs lem-sfb-simplex-lattice-shuffle-boundary: the existing lemma proves a shuffle boundary identity between universal simplices, not the cohomology or contraction of the rational polynomial additive bar.

lem-sfb-internal-bar-ordered-cup vs lem-sfb-condensed-derived-restriction-calculus: the existing statement gives cup functoriality and degree-one character normalization but does not assert that the PRODUCT of continuous cocycles represents the specified higher derived cup arrow under the bar augmentation. The new lemma is precisely this generic internal comparison, without any acyclicity calculation.

lem-sfb-internal-bar-ordered-cup vs lem-sfb-bicosimplicial-shuffle-totalization: the existing statement identifies a signed bicosimplicial totalization comparison; it does not identify the coefficient-multiplication cup product with the internal derived cup or connecting characters.

Whole-DAG key-word searches and blueprint_refs.py searches for continuous cochains, polynomial cochains, polynomial, symmetric coalgebra, derived internal bar, Koszul, bar cup and cup product were inspected. The matching blueprint nodes concern other coefficient categories or geometric cup constructions; none states the new inputs. No new Stacks-tag duplicate was introduced: no exact Stacks tag was found for the new obligations, so none is falsely claimed.

## Review by Q09

I read coord/delivery-errors.md B–E in full and compared the item and each new statement with the current main-20261015 proof paragraph (3). That paragraph delegates nonfinite open direct image to an open-coefficient theorem; it does not contain the noncomplete analytic calculation. Accordingly the three new sources explicitly say what is missing, and the item proof is agent-written. I read the complete statements of every proof citation: the existing derived-bar theorem retains derived internal Hom, and the restriction-calculus theorem normalizes the connecting class but supplies no continuous-cochain acyclicity. I corrected the initial temptation to use either as an analytic comparison by stating that missing comparison separately, and I separated the higher cup/bar identification as well.

For step 1 the two new statements specify the identical polynomial complex, including the number and indexing of variables, all signs of the inhomogeneous differential, and the ordered monomial inclusion. Its based complex K is literally the item's finite direct-sum complex; no exterior-basis theorem is assumed. In step 2 the algebraic statement explicitly gives rational finite-support maps and their homotopy identities. I checked that extending such maps to internal sums is coefficientwise, natural on profinite parameters, and requires neither exact scalar extension nor convergence. Thus the derived equivalence is obtained from a homotopy, not inferred only from per-degree isomorphisms.

For step 3 the analytic node has exactly both requested fields, their norm topologies, all continuous maps, the correct profinite lattice and ordinary internal coefficient category. The map is polynomial evaluation followed by the canonical underived-to-derived map on one compatible equivariant injective resolution. It is a derived-object comparison and does not erase higher internal-Hom terms. Step 4 uses exactly the augmentation isomorphism stated by lem-sfb-condensed-derived-invariant-bar; L is profinite, A is commutative, the action is trivial, and the same bounded-below compatible model and coefficient-universe conditions hold. The orientation of epsilon and its inverse was checked explicitly.

For step 5 the new generic bar/cup statement identifies the actual arrow from A[-q], not just its cohomology. Its hypotheses apply to each ordered list of coordinate additive maps, and the restriction-calculus statement uses the same sign for the degree-one cocycle. Evaluation gives the product with the first character in the first group argument, in precisely the order required. Composing with epsilon inverse and checking the finitely many summand maps gives equality with chi, including the unit. For step 6 the action of the trivial group and its invariant inclusion are both literally identities, which proves the special identity clause directly.

I checked small cases of every new statement. For the analytic comparison r=0 reduces to the unit and the unnormalized constant cosimplicial bar; no positive-dimensional comparison is inferred from that check. Coordinate degree-one maps are continuous and additive for both F; this check does not assume completeness. For the algebraic statement I checked r=0, the zero algebra, degree-zero cancellation, the ordered projection's signs, pi=1 on generators, and the relations d(x_i x_j)=-(x_i y_j+x_j y_i), including the repeated-index case. The sandbox Python calculation checked d²=0, pd=0 and the expected cohomology in 48 finite multidegree cases for r=0,1,2 through cochain degree 3; this is only a sanity check, not a proof of the unsplit universal contraction. For the cup node I checked the empty list/unit, one character/connecting class, zero characters, and the order of a two-character product, with no characteristic restriction and no division by a factorial. These checks found no counterexample. The unproved analytic comparison is deliberately a visible obligation, not a purported theorem supplied by an unavailable source.

All three new nodes have self-contained statements, empty proof and proof_deps, real recorded searches, and populated blueprint references. There are no new definitions containing hidden data or proof claims. I compared the dependency direction with the parent dense-lattice theorem to avoid a cycle. Every proof citation has a verbatim quotation in citations.json. No proof step exceeds 2000 characters (the longest is under 900), and every non-elementary comparison used by those steps has its own cited statement. The differences from nearby DAG nodes are recorded above, including the same-route statements whose hypotheses are too weak to supply the missing analytic or cup input.
