# Worker report: lem-sfb-polynomial-zero-section-dimension

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-polynomial-zero-section-dimension.json: statement, split into four proof steps; no exact Mathlib or project declaration found. Original statement, statement dependencies, source, ancestry and inherited search records retained.
- citations.json: nine verbatim statement quotations, one for every step/node pair.
- searches.jsonl: actual msearch.py results, also recorded in mathlib_searches.

New nodes: 0. New Mathlib leaves: 0. The proof reuses the existing Mathlib leaf lem-sf-noetherian-polynomial-dimension (MvPolynomial.ringKrullDim_of_isNoetherianRing, Mathlib/RingTheory/KrullDimension/Polynomial.lean:120-121).

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, dimensionAt/dimensionAtPoint/topologicalKrullDimAt, and zero-section dimension names. Existing dimension-at-point-components and regular-sequence statements give tools, rather than this item's entire assertion. A declaration with sorry is not treated as finished.

## WANTED

None.

## Corrections and route

No statement correction or dispute. The statement concerns the minimum of dimensions of open neighbourhoods, not the dimension of a local ring. Using height alone would be wrong: for B=k[t] and q=(0), the dimension at q is 1 although the local ring is a field of dimension 0.

The inherited source's component method is retained. I read Stacks algebra.tex Tag 00OT (lemma-dimension-at-a-point-finite-type-over-field), including its component-maximum proof, and Tag 00P0 (lemma-dimension-prime-polynomial-ring). The existing polynomial-dimension Mathlib leaf replaces an unnecessary passage through transcendence degrees to compute each polynomial component's dimension. Below this node the unit route is unchanged. I also read the latest blueprint's sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md and sk-thm-sf-ctf-stability-direct-images.proof.md: this is a supporting dimension computation for the recorded alteration/deformation chain, not a new six-functor argument. The inherited blueprint.from.node is null, as tools/blueprint_refs.py ancestor also reports; I preserved its existing precise place and via chain.

The four generic off-unit inputs (finite-type Noetherianity, a minimal prime below a prime, polynomial-domain permanence, and Tag 00OT) are declared in split_report.tool_uses with reasons. The already existing polynomial-dimension leaf is a tool automatically. No SGA source is used.

## Not duplicates

No nodes created. Whole-DAG statement/title/tag searches located and reused lem-weil-pbc-dimension-at-point-components (00OT), lem-sf-noetherian-polynomial-dimension, lem-weil-pbc-prime-contains-minimal-prime, lem-weil-pbc-polynomial-ring-domain and lem-weil-pbc-finite-type-algebra-noetherian. I searched the whole imported blueprint with blueprint_refs.py for 'dimension at a point', 'dimension polynomial', 'polynomial' and 'zero section'. No blueprint node states the item in another form. The initially considered polynomial-component helper was not created: once the prime-existence and domain results are cited, its proof is a few lines, which belongs in the item's step 2.

## Review by NI

I read delivery-errors.md B through E, including the repeated new-target section, against the final JSON. There are no new statement-only nodes to audit or duplicated clauses to conceal the item. Every non-elementary input is an existing cited statement. No step exceeds 2000 characters (lengths 516, 973, 586, 809). The component correspondence in step 2 is a direct ideal argument, not an unnamed comparison theorem: both directions and the zero-section containment condition are written out.

Step 1 uses the finite-type-algebra definition to append the r variables to finite generators of B, and the polynomial-ring definition to evaluate at zero. I checked their complete statements: the latter includes the coefficient formula and universal property. The composite map to B/q is onto (constants lift every residue class), and its kernel is exactly qC+(x_1,...,x_r), since subtracting the constant term leaves an element of the variable ideal. Its quotient is the nonzero domain B/q because q is prime, so Q really is a point. No reducedness assumption is used.

Step 2 uses exactly the domain assertion of lem-weil-pbc-polynomial-ring-domain, and the I=0 assertion of lem-weil-pbc-prime-contains-minimal-prime, whose statements I opened. I read the latter's source Tag 00E0(4), lemma-Zariski-topology in algebra.tex, and the polynomial-domain node's source Tag 09ZD, lemma-integral-cover-trivial-cohomology in etale-cohomology.tex, where the polynomial fraction field is used. The coefficient-reduction map has kernel aC because each coefficient in a multiplies a monomial. Thus extension of a prime is prime. For a minimal polynomial prime P, the chosen minimal a below P intersect B gives aC contained in P and hence equality. Conversely, a prime below aC contracts to a prime below minimal a, so has contraction a and contains aC. Finally extension/contraction yields aC contained in Q exactly when a is contained in q. These deductions require neither a domain B nor a closed point q.

Step 3 applies finite-type Noetherianity only to B/a over the Noetherian field k, with finite generators explicitly supplied. I read Tag 00FN, lemma-Noetherian-permanence in algebra.tex, and the exact node statement. I read Mathlib/RingTheory/KrullDimension/Polynomial.lean:120-121 and the existing leaf statement: it allows every Noetherian coefficient ring and every finite variable set, including zero variables. Therefore it applies to B/a with exactly r variables. The quotient-ring isomorphism of step 2 gives an order isomorphism on prime chains, which justifies transporting ring dimension without invoking an uncited comparison theorem.

Step 4 uses the actual minimal-prime formula, finiteness, nonemptiness and nonnegative-integral dimension assertion in lem-weil-pbc-dimension-at-point-components; its full statement is quoted in citations.json. It applies to B by hypothesis and C by step 1. The two lists of minimal primes match by step 2. Taking the maximum after adding the same natural r proves the desired equality; the maximum is finite and attained, not an unjustified supremum interchange. This is the only conversion from ring dimensions of component quotients to dimensions at the two points.

Edge cases: r=0 gives C=B and Q=q, so equality is tautological. If B=0 no prime exists. For B=k[epsilon]/(epsilon^2), the single minimal component has dimension zero and its polynomial extension has dimension r; no reducedness was used. For B=k[u,v,w]/((u) intersect (v,w)) at (u,v,w), the two component dimensions are 2 and 1, and the formula compares max(2+r,1+r) with 2+r. At q=(v,w), only the one-dimensional component lies below q, and the result is 1+r, demonstrating why global dim B+r cannot replace the local component maximum. For B=k[t] at q=(0), the two dimensions are 1 and 1+r despite local-ring dimension zero on the base. All arguments are independent of perfectness of k.

I ran the required semantic, Loogle and grep searches using msearch.py, read the returned declarations, then tried a second phrasing. The global Noetherian polynomial theorem is a genuine component tool and already has a node; smooth-relative-dimension and submersive-presentation hits do not state this topological dimension-at-a-point assertion. The exploratory minimal-prime hits concern quotient/localization operations, not this polynomial component bijection; I kept its elementary argument rather than inventing a leaf. Inherited searches remain intact and the new queries exactly match searches.jsonl.

## Unfinished work

None in the one-level stage-1 split. Existing dependencies retain their own current statuses. No Lean source or repository file was written and no compiler or build tool was run. Delivery validation results are recorded below.

## Validation

Server review_split: PASS, 0 new nodes. Required deliver.py --no-push exited 0 and printed OK (not pushed), preflight passed, at 32e307c70e9. The diagnostic notes that the inherited unit has no realization recorded yet; this supporting node is not the unit's key statement, so its realization record is outside this delivery.
